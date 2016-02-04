
open Prims
type binding =
| Binding_var of FStar_Syntax_Syntax.bv
| Binding_lid of (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme)
| Binding_sig of (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
| Binding_univ of FStar_Syntax_Syntax.univ_name
| Binding_sig_inst of (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes)

let is_Binding_var : binding  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_lid : binding  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Binding_lid (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_sig : binding  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Binding_sig (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_univ : binding  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Binding_univ (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_sig_inst : binding  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Binding_sig_inst (_) -> begin
true
end
| _ -> begin
false
end))

let ___Binding_var____0 : binding  ->  FStar_Syntax_Syntax.bv = (fun projectee -> (match (projectee) with
| Binding_var (_84_15) -> begin
_84_15
end))

let ___Binding_lid____0 : binding  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme) = (fun projectee -> (match (projectee) with
| Binding_lid (_84_18) -> begin
_84_18
end))

let ___Binding_sig____0 : binding  ->  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt) = (fun projectee -> (match (projectee) with
| Binding_sig (_84_21) -> begin
_84_21
end))

let ___Binding_univ____0 : binding  ->  FStar_Syntax_Syntax.univ_name = (fun projectee -> (match (projectee) with
| Binding_univ (_84_24) -> begin
_84_24
end))

let ___Binding_sig_inst____0 : binding  ->  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes) = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_84_27) -> begin
_84_27
end))

type delta_level =
| NoDelta
| OnlyInline
| Unfold

let is_NoDelta : delta_level  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| NoDelta -> begin
true
end
| _ -> begin
false
end))

let is_OnlyInline : delta_level  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| OnlyInline -> begin
true
end
| _ -> begin
false
end))

let is_Unfold : delta_level  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Unfold -> begin
true
end
| _ -> begin
false
end))

let visible_at : delta_level  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun d q -> (match ((d, q)) with
| ((NoDelta, _)) | ((OnlyInline, FStar_Syntax_Syntax.Inline)) | ((Unfold, FStar_Syntax_Syntax.Inline)) | ((Unfold, FStar_Syntax_Syntax.Unfoldable)) -> begin
true
end
| _84_44 -> begin
false
end))

let glb_delta : delta_level  ->  delta_level  ->  delta_level = (fun d1 d2 -> (match ((d1, d2)) with
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

let is_Mkedge : edge  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkedge"))))

type effects =
{decls : FStar_Syntax_Syntax.eff_decl Prims.list; order : edge Prims.list; joins : (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list}

let is_Mkeffects : effects  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeffects"))))

type cached_elt =
((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either

type env =
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ Prims.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap Prims.list; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; default_effects : (FStar_Ident.lident * FStar_Ident.lident) Prims.list; type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t); use_bv_sorts : Prims.bool} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit; solve : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit} 
 and guard_t =
{guard_f : FStar_TypeChecker_Common.guard_formula; deferred : FStar_TypeChecker_Common.deferred; univ_ineqs : FStar_TypeChecker_Common.univ_ineq Prims.list; implicits : (env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list}

let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

let is_Mksolver_t : solver_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksolver_t"))))

let is_Mkguard_t : guard_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkguard_t"))))

type env_t =
env

type implicits =
(env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list

type sigtable =
FStar_Syntax_Syntax.sigelt FStar_Util.smap

let default_table_size : Prims.int = 200

let new_sigtab = (fun _84_114 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))

let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t))  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun tc solver module_lid -> (let _187_359 = (FStar_Util.smap_create 100)
in (let _187_358 = (let _187_357 = (new_sigtab ())
in (_187_357)::[])
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _187_359; modules = []; expected_typ = None; sigtab = _187_358; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []; type_of = tc; use_bv_sorts = false})))

let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> (FStar_List.hd env.sigtab))

let push : env  ->  Prims.string  ->  env = (fun env msg -> (let _84_121 = (env.solver.push msg)
in (let _84_123 = env
in (let _187_368 = (let _187_367 = (let _187_366 = (sigtab env)
in (FStar_Util.smap_copy _187_366))
in (_187_367)::env.sigtab)
in {solver = _84_123.solver; range = _84_123.range; curmodule = _84_123.curmodule; gamma = _84_123.gamma; gamma_cache = _84_123.gamma_cache; modules = _84_123.modules; expected_typ = _84_123.expected_typ; sigtab = _187_368; is_pattern = _84_123.is_pattern; instantiate_imp = _84_123.instantiate_imp; effects = _84_123.effects; generalize = _84_123.generalize; letrecs = _84_123.letrecs; top_level = _84_123.top_level; check_uvars = _84_123.check_uvars; use_eq = _84_123.use_eq; is_iface = _84_123.is_iface; admit = _84_123.admit; default_effects = _84_123.default_effects; type_of = _84_123.type_of; use_bv_sorts = _84_123.use_bv_sorts}))))

let mark : env  ->  env = (fun env -> (let _84_126 = (env.solver.mark "USER MARK")
in (let _84_128 = env
in (let _187_373 = (let _187_372 = (let _187_371 = (sigtab env)
in (FStar_Util.smap_copy _187_371))
in (_187_372)::env.sigtab)
in {solver = _84_128.solver; range = _84_128.range; curmodule = _84_128.curmodule; gamma = _84_128.gamma; gamma_cache = _84_128.gamma_cache; modules = _84_128.modules; expected_typ = _84_128.expected_typ; sigtab = _187_373; is_pattern = _84_128.is_pattern; instantiate_imp = _84_128.instantiate_imp; effects = _84_128.effects; generalize = _84_128.generalize; letrecs = _84_128.letrecs; top_level = _84_128.top_level; check_uvars = _84_128.check_uvars; use_eq = _84_128.use_eq; is_iface = _84_128.is_iface; admit = _84_128.admit; default_effects = _84_128.default_effects; type_of = _84_128.type_of; use_bv_sorts = _84_128.use_bv_sorts}))))

let commit_mark : env  ->  env = (fun env -> (let _84_131 = (env.solver.commit_mark "USER MARK")
in (let sigtab = (match (env.sigtab) with
| hd::_84_135::tl -> begin
(hd)::tl
end
| _84_140 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _84_142 = env
in {solver = _84_142.solver; range = _84_142.range; curmodule = _84_142.curmodule; gamma = _84_142.gamma; gamma_cache = _84_142.gamma_cache; modules = _84_142.modules; expected_typ = _84_142.expected_typ; sigtab = sigtab; is_pattern = _84_142.is_pattern; instantiate_imp = _84_142.instantiate_imp; effects = _84_142.effects; generalize = _84_142.generalize; letrecs = _84_142.letrecs; top_level = _84_142.top_level; check_uvars = _84_142.check_uvars; use_eq = _84_142.use_eq; is_iface = _84_142.is_iface; admit = _84_142.admit; default_effects = _84_142.default_effects; type_of = _84_142.type_of; use_bv_sorts = _84_142.use_bv_sorts}))))

let reset_mark : env  ->  env = (fun env -> (let _84_145 = (env.solver.reset_mark "USER MARK")
in (let _84_147 = env
in (let _187_378 = (FStar_List.tl env.sigtab)
in {solver = _84_147.solver; range = _84_147.range; curmodule = _84_147.curmodule; gamma = _84_147.gamma; gamma_cache = _84_147.gamma_cache; modules = _84_147.modules; expected_typ = _84_147.expected_typ; sigtab = _187_378; is_pattern = _84_147.is_pattern; instantiate_imp = _84_147.instantiate_imp; effects = _84_147.effects; generalize = _84_147.generalize; letrecs = _84_147.letrecs; top_level = _84_147.top_level; check_uvars = _84_147.check_uvars; use_eq = _84_147.use_eq; is_iface = _84_147.is_iface; admit = _84_147.admit; default_effects = _84_147.default_effects; type_of = _84_147.type_of; use_bv_sorts = _84_147.use_bv_sorts}))))

let pop : env  ->  Prims.string  ->  env = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(FStar_All.failwith "Too many pops")
end
| _84_157::tl -> begin
(let _84_159 = (env.solver.pop msg)
in (let _84_161 = env
in {solver = _84_161.solver; range = _84_161.range; curmodule = _84_161.curmodule; gamma = _84_161.gamma; gamma_cache = _84_161.gamma_cache; modules = _84_161.modules; expected_typ = _84_161.expected_typ; sigtab = tl; is_pattern = _84_161.is_pattern; instantiate_imp = _84_161.instantiate_imp; effects = _84_161.effects; generalize = _84_161.generalize; letrecs = _84_161.letrecs; top_level = _84_161.top_level; check_uvars = _84_161.check_uvars; use_eq = _84_161.use_eq; is_iface = _84_161.is_iface; admit = _84_161.admit; default_effects = _84_161.default_effects; type_of = _84_161.type_of; use_bv_sorts = _84_161.use_bv_sorts}))
end))

let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> ((let _187_388 = (FStar_ST.read FStar_Options.debug)
in (FStar_All.pipe_right _187_388 (FStar_Util.for_some (fun x -> ((env.curmodule.FStar_Ident.str = "") || (env.curmodule.FStar_Ident.str = x)))))) && (FStar_Options.debug_level_geq l)))

let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(let _84_168 = e
in {solver = _84_168.solver; range = r; curmodule = _84_168.curmodule; gamma = _84_168.gamma; gamma_cache = _84_168.gamma_cache; modules = _84_168.modules; expected_typ = _84_168.expected_typ; sigtab = _84_168.sigtab; is_pattern = _84_168.is_pattern; instantiate_imp = _84_168.instantiate_imp; effects = _84_168.effects; generalize = _84_168.generalize; letrecs = _84_168.letrecs; top_level = _84_168.top_level; check_uvars = _84_168.check_uvars; use_eq = _84_168.use_eq; is_iface = _84_168.is_iface; admit = _84_168.admit; default_effects = _84_168.default_effects; type_of = _84_168.type_of; use_bv_sorts = _84_168.use_bv_sorts})
end)

let get_range : env  ->  FStar_Range.range = (fun e -> e.range)

let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)

let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)

let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (let _84_175 = env
in {solver = _84_175.solver; range = _84_175.range; curmodule = lid; gamma = _84_175.gamma; gamma_cache = _84_175.gamma_cache; modules = _84_175.modules; expected_typ = _84_175.expected_typ; sigtab = _84_175.sigtab; is_pattern = _84_175.is_pattern; instantiate_imp = _84_175.instantiate_imp; effects = _84_175.effects; generalize = _84_175.generalize; letrecs = _84_175.letrecs; top_level = _84_175.top_level; check_uvars = _84_175.check_uvars; use_eq = _84_175.use_eq; is_iface = _84_175.is_iface; admit = _84_175.admit; default_effects = _84_175.default_effects; type_of = _84_175.type_of; use_bv_sorts = _84_175.use_bv_sorts}))

let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))

let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (let _187_412 = (sigtab env)
in (FStar_Util.smap_try_find _187_412 (FStar_Ident.text_of_lid lid))))

let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))

let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _187_417 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _187_417)))

let new_u_univ = (fun _84_184 -> (let _187_419 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_187_419)))

let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match ((ts, us)) with
| (([], t), []) -> begin
([], t)
end
| ((formals, t), _84_197) -> begin
(let _84_199 = ()
in (let n = ((FStar_List.length formals) - 1)
in (let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN (((n - i), u)))))
in (let _187_426 = (FStar_Syntax_Subst.subst vs t)
in (us, _187_426)))))
end))

let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _84_1 -> (match (_84_1) with
| ([], t) -> begin
([], t)
end
| (us, t) -> begin
(let us' = (FStar_All.pipe_right us (FStar_List.map (fun _84_212 -> (new_u_univ ()))))
in (inst_tscheme_with (us, t) us'))
end))

let inst_effect_fun : env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun env ed _84_219 -> (match (_84_219) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(let _187_436 = (inst_tscheme ((FStar_List.append ed.FStar_Syntax_Syntax.univs us), t))
in (Prims.snd _187_436))
end
| _84_222 -> begin
(let _187_438 = (let _187_437 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _187_437))
in (FStar_All.failwith _187_438))
end)
end))

type tri =
| Yes
| No
| Maybe

let is_Yes : tri  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Yes -> begin
true
end
| _ -> begin
false
end))

let is_No : tri  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| No -> begin
true
end
| _ -> begin
false
end))

let is_Maybe : tri  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Maybe -> begin
true
end
| _ -> begin
false
end))

let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (let cur = (current_module env)
in if (l.FStar_Ident.nsstr = cur.FStar_Ident.str) then begin
Yes
end else begin
if (FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str) then begin
(let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (let rec aux = (fun c l -> (match ((c, l)) with
| ([], _84_233) -> begin
Maybe
end
| (_84_236, []) -> begin
No
end
| (hd::tl, hd'::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _84_247 -> begin
No
end))
in (aux cur lns))))
end else begin
No
end
end))

let lookup_qname : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either Prims.option = (fun env lid -> (let cur_mod = (in_cur_mod env lid)
in (let cache = (fun t -> (let _84_253 = (FStar_Util.smap_add env.gamma_cache lid.FStar_Ident.str t)
in Some (t)))
in (let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find env.gamma_cache lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _84_2 -> (match (_84_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _187_458 = (let _187_457 = (inst_tscheme t)
in FStar_Util.Inl (_187_457))
in Some (_187_458))
end else begin
None
end
end
| Binding_sig (_84_262, FStar_Syntax_Syntax.Sig_bundle (ses, _84_265, _84_267, _84_269)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _187_460 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _187_460 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr ((se, None))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_84_282) -> begin
Some (t)
end
| _84_285 -> begin
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
| _84_292 -> begin
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

let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _84_302, _84_304, _84_306) -> begin
(add_sigelts env ses)
end
| _84_310 -> begin
(let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _187_470 = (sigtab env)
in (FStar_Util.smap_add _187_470 l.FStar_Ident.str se))) lids))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))

let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun _84_3 -> (match (_84_3) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _84_321 -> begin
None
end))))

let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _84_4 -> (match (_84_4) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _84_328 -> begin
false
end)) env.gamma) FStar_Option.isSome))

let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_84_332, lb::[]), _84_337, _84_339, _84_341) -> begin
(let _187_490 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_187_490))
end
| FStar_Syntax_Syntax.Sig_let ((_84_345, lbs), _84_349, _84_351, _84_353) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_84_358) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (lid') -> begin
if (FStar_Ident.lid_equals lid lid') then begin
(let _187_492 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_187_492))
end else begin
None
end
end)))
end
| _84_363 -> begin
None
end))

let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _187_500 = (let _187_499 = (let _187_498 = (variable_not_found bv)
in (let _187_497 = (FStar_Syntax_Syntax.range_of_bv bv)
in (_187_498, _187_497)))
in FStar_Syntax_Syntax.Error (_187_499))
in (Prims.raise _187_500))
end
| Some (t) -> begin
t
end))

let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _84_372) -> begin
(let _187_506 = (let _187_505 = (let _187_504 = (let _187_503 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _187_503))
in (ne.FStar_Syntax_Syntax.univs, _187_504))
in (inst_tscheme _187_505))
in Some (_187_506))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _84_379, _84_381, _84_383) -> begin
(let _187_510 = (let _187_509 = (let _187_508 = (let _187_507 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _187_507))
in (us, _187_508))
in (inst_tscheme _187_509))
in Some (_187_510))
end
| _84_387 -> begin
None
end))

let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_84_397, t) -> begin
Some (t)
end)
end
| _84_402 -> begin
None
end))

let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env lid -> (let mapper = (fun _84_5 -> (match (_84_5) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_84_409, uvs, t, _84_413, _84_415, _84_417, _84_419, _84_421), None) -> begin
(let _187_521 = (inst_tscheme (uvs, t))
in Some (_187_521))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _84_432), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _187_522 = (inst_tscheme (uvs, t))
in Some (_187_522))
end else begin
None
end
end else begin
(let _187_523 = (inst_tscheme (uvs, t))
in Some (_187_523))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _84_443, _84_445, _84_447, _84_449), None) -> begin
(match (tps) with
| [] -> begin
(let _187_525 = (inst_tscheme (uvs, k))
in (FStar_All.pipe_left (fun _187_524 -> Some (_187_524)) _187_525))
end
| _84_457 -> begin
(let _187_530 = (let _187_529 = (let _187_528 = (let _187_527 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _187_527))
in (uvs, _187_528))
in (inst_tscheme _187_529))
in (FStar_All.pipe_left (fun _187_526 -> Some (_187_526)) _187_530))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _84_463, _84_465, _84_467, _84_469), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _187_532 = (inst_tscheme_with (uvs, k) us)
in (FStar_All.pipe_left (fun _187_531 -> Some (_187_531)) _187_532))
end
| _84_478 -> begin
(let _187_537 = (let _187_536 = (let _187_535 = (let _187_534 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _187_534))
in (uvs, _187_535))
in (inst_tscheme_with _187_536 us))
in (FStar_All.pipe_left (fun _187_533 -> Some (_187_533)) _187_537))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_84_482), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _84_487 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _187_538 = (lookup_qname env lid)
in (FStar_Util.bind_opt _187_538 mapper))) with
| Some (us, t) -> begin
Some ((us, (let _84_493 = t
in {FStar_Syntax_Syntax.n = _84_493.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _84_493.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _84_493.FStar_Syntax_Syntax.vars})))
end
| None -> begin
None
end)))

let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _187_545 = (let _187_544 = (let _187_543 = (name_not_found l)
in (_187_543, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_187_544))
in (Prims.raise _187_545))
end
| Some (x) -> begin
x
end))

let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_84_504, uvs, t, _84_508, _84_510), None)) -> begin
(inst_tscheme (uvs, t))
end
| _84_518 -> begin
(let _187_552 = (let _187_551 = (let _187_550 = (name_not_found lid)
in (_187_550, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_187_551))
in (Prims.raise _187_552))
end))

let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_84_522, uvs, t, _84_526, _84_528, _84_530, _84_532, _84_534), None)) -> begin
(inst_tscheme (uvs, t))
end
| _84_542 -> begin
(let _187_559 = (let _187_558 = (let _187_557 = (name_not_found lid)
in (_187_557, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_187_558))
in (Prims.raise _187_559))
end))

let lookup_definition : delta_level  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_84_552, lbs), _84_556, _84_558, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (let lid' = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Ident.lid_equals lid lid') then begin
(let _187_568 = (let _187_567 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (lb.FStar_Syntax_Syntax.lbunivs, _187_567))
in Some (_187_568))
end else begin
None
end)))
end
| _84_565 -> begin
None
end)
end
| _84_567 -> begin
None
end))

let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _187_575 = (let _187_574 = (let _187_573 = (name_not_found ftv)
in (_187_573, (FStar_Ident.range_of_lid ftv)))
in FStar_Syntax_Syntax.Error (_187_574))
in (Prims.raise _187_575))
end
| Some (k) -> begin
k
end))

let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (let fail = (fun _84_577 -> (match (()) with
| () -> begin
(let _187_586 = (let _187_585 = (FStar_Util.string_of_int i)
in (let _187_584 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _187_585 _187_584)))
in (FStar_All.failwith _187_586))
end))
in (let _84_581 = (lookup_datacon env lid)
in (match (_84_581) with
| (_84_579, t) -> begin
(match ((let _187_587 = (FStar_Syntax_Subst.compress t)
in _187_587.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _84_584) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(let b = (FStar_List.nth binders i)
in (let _187_588 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _187_588 Prims.fst)))
end
end
| _84_589 -> begin
(fail ())
end)
end))))

let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_84_593, uvs, t, q, _84_598), None)) -> begin
Some (((uvs, t), q))
end
| _84_606 -> begin
None
end))

let lookup_effect_abbrev : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _84_615), None)) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _84_6 -> (match (_84_6) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _84_625 -> begin
false
end)))) then begin
None
end else begin
(let _84_630 = (FStar_Syntax_Util.open_univ_vars_binders_and_comp univs binders c)
in (match (_84_630) with
| (_84_627, binders, c) -> begin
Some ((binders, c))
end))
end
end
| _84_632 -> begin
None
end))

let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_84_636, _84_638, _84_640, _84_642, _84_644, dcs, _84_647, _84_649), _84_653)) -> begin
dcs
end
| _84_658 -> begin
[]
end))

let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_84_662, _84_664, _84_666, l, _84_669, _84_671, _84_673, _84_675), _84_679)) -> begin
l
end
| _84_684 -> begin
(let _187_607 = (let _187_606 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _187_606))
in (FStar_All.failwith _187_607))
end))

let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_84_688, _84_690, _84_692, _84_694, _84_696, _84_698, _84_700, _84_702), _84_706)) -> begin
true
end
| _84_711 -> begin
false
end))

let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_84_715, _84_717, _84_719, _84_721, _84_723, _84_725, tags, _84_728), _84_732)) -> begin
(FStar_Util.for_some (fun _84_7 -> (match (_84_7) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _84_744 -> begin
false
end)) tags)
end
| _84_746 -> begin
false
end))

let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_84_750, _84_752, _84_754, quals, _84_757), _84_761)) -> begin
(FStar_Util.for_some (fun _84_8 -> (match (_84_8) with
| FStar_Syntax_Syntax.Projector (_84_767) -> begin
true
end
| _84_770 -> begin
false
end)) quals)
end
| _84_772 -> begin
false
end))

let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))

let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _187_633 = (let _187_632 = (let _187_631 = (name_not_found l)
in (_187_631, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_187_632))
in (Prims.raise _187_633))
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
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _84_800 -> (match (_84_800) with
| (m1, m2, _84_795, _84_797, _84_799) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _187_709 = (let _187_708 = (let _187_707 = (let _187_706 = (FStar_Syntax_Print.lid_to_string l1)
in (let _187_705 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _187_706 _187_705)))
in (_187_707, env.range))
in FStar_Syntax_Syntax.Error (_187_708))
in (Prims.raise _187_709))
end
| Some (_84_803, _84_805, m3, j1, j2) -> begin
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
(let _187_724 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _187_724))
end
| Some (md) -> begin
(let _84_826 = (inst_tscheme (md.FStar_Syntax_Syntax.univs, md.FStar_Syntax_Syntax.signature))
in (match (_84_826) with
| (_84_824, s) -> begin
(let s = (FStar_Syntax_Subst.compress s)
in (match ((md.FStar_Syntax_Syntax.binders, s.FStar_Syntax_Syntax.n)) with
| ([], FStar_Syntax_Syntax.Tm_arrow ((a, _84_839)::(wp, _84_835)::(wlp, _84_831)::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _84_847 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))

let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))

let default_effect : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (FStar_Util.find_map env.default_effects (fun _84_854 -> (match (_84_854) with
| (l', m) -> begin
if (FStar_Ident.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))

let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, _84_859, _84_861, c, quals, r) -> begin
(match ((FStar_Util.find_map quals (fun _84_9 -> (match (_84_9) with
| FStar_Syntax_Syntax.DefaultEffect (n) -> begin
n
end
| _84_871 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(let _84_875 = env
in {solver = _84_875.solver; range = _84_875.range; curmodule = _84_875.curmodule; gamma = _84_875.gamma; gamma_cache = _84_875.gamma_cache; modules = _84_875.modules; expected_typ = _84_875.expected_typ; sigtab = _84_875.sigtab; is_pattern = _84_875.is_pattern; instantiate_imp = _84_875.instantiate_imp; effects = _84_875.effects; generalize = _84_875.generalize; letrecs = _84_875.letrecs; top_level = _84_875.top_level; check_uvars = _84_875.check_uvars; use_eq = _84_875.use_eq; is_iface = _84_875.is_iface; admit = _84_875.admit; default_effects = ((e, l))::env.default_effects; type_of = _84_875.type_of; use_bv_sorts = _84_875.use_bv_sorts})
end)
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _84_879) -> begin
(let effects = (let _84_882 = env.effects
in {decls = (ne)::env.effects.decls; order = _84_882.order; joins = _84_882.joins})
in (let _84_885 = env
in {solver = _84_885.solver; range = _84_885.range; curmodule = _84_885.curmodule; gamma = _84_885.gamma; gamma_cache = _84_885.gamma_cache; modules = _84_885.modules; expected_typ = _84_885.expected_typ; sigtab = _84_885.sigtab; is_pattern = _84_885.is_pattern; instantiate_imp = _84_885.instantiate_imp; effects = effects; generalize = _84_885.generalize; letrecs = _84_885.letrecs; top_level = _84_885.top_level; check_uvars = _84_885.check_uvars; use_eq = _84_885.use_eq; is_iface = _84_885.is_iface; admit = _84_885.admit; default_effects = _84_885.default_effects; type_of = _84_885.type_of; use_bv_sorts = _84_885.use_bv_sorts}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _84_889) -> begin
(let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _187_745 = (e1.mlift r wp1)
in (e2.mlift r _187_745)))})
in (let mk_lift = (fun lift_t r wp1 -> (let _84_904 = (inst_tscheme lift_t)
in (match (_84_904) with
| (_84_902, lift_t) -> begin
(let _187_757 = (let _187_756 = (let _187_755 = (let _187_754 = (FStar_Syntax_Syntax.as_arg r)
in (let _187_753 = (let _187_752 = (FStar_Syntax_Syntax.as_arg wp1)
in (_187_752)::[])
in (_187_754)::_187_753))
in (lift_t, _187_755))
in FStar_Syntax_Syntax.Tm_app (_187_756))
in (FStar_Syntax_Syntax.mk _187_757 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub.FStar_Syntax_Syntax.lift)}
in (let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (let print_mlift = (fun l -> (let arg = (let _187_774 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _187_774 None))
in (let wp = (let _187_775 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _187_775 None))
in (let _187_776 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _187_776)))))
in (let order = (edge)::env.effects.order
in (let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (let find_edge = (fun order _84_921 -> (match (_84_921) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _187_782 -> Some (_187_782)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _187_790 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _187_789 = (find_edge order (i, k))
in (let _187_788 = (find_edge order (k, j))
in (_187_789, _187_788)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _84_933 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _187_790))) order))
in (let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _187_882 = (find_edge order (i, k))
in (let _187_881 = (find_edge order (j, k))
in (_187_882, _187_881)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _84_950, _84_952) -> begin
if ((let _187_883 = (find_edge order (k, ub))
in (FStar_Util.is_some _187_883)) && (not ((let _187_884 = (find_edge order (ub, k))
in (FStar_Util.is_some _187_884))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _84_956 -> begin
bopt
end)) None))
in (match (join_opt) with
| None -> begin
[]
end
| Some (k, e1, e2) -> begin
((i, j, k, e1.mlift, e2.mlift))::[]
end))))))))
in (let effects = (let _84_965 = env.effects
in {decls = _84_965.decls; order = order; joins = joins})
in (let _84_968 = env
in {solver = _84_968.solver; range = _84_968.range; curmodule = _84_968.curmodule; gamma = _84_968.gamma; gamma_cache = _84_968.gamma_cache; modules = _84_968.modules; expected_typ = _84_968.expected_typ; sigtab = _84_968.sigtab; is_pattern = _84_968.is_pattern; instantiate_imp = _84_968.instantiate_imp; effects = effects; generalize = _84_968.generalize; letrecs = _84_968.letrecs; top_level = _84_968.top_level; check_uvars = _84_968.check_uvars; use_eq = _84_968.use_eq; is_iface = _84_968.is_iface; admit = _84_968.admit; default_effects = _84_968.default_effects; type_of = _84_968.type_of; use_bv_sorts = _84_968.use_bv_sorts})))))))))))))
end
| _84_971 -> begin
env
end))

let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (let _187_933 = (let _84_974 = env
in (let _187_932 = (let _187_931 = (let _187_930 = (let _187_929 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_187_929, s))
in Binding_sig (_187_930))
in (_187_931)::env.gamma)
in {solver = _84_974.solver; range = _84_974.range; curmodule = _84_974.curmodule; gamma = _187_932; gamma_cache = _84_974.gamma_cache; modules = _84_974.modules; expected_typ = _84_974.expected_typ; sigtab = _84_974.sigtab; is_pattern = _84_974.is_pattern; instantiate_imp = _84_974.instantiate_imp; effects = _84_974.effects; generalize = _84_974.generalize; letrecs = _84_974.letrecs; top_level = _84_974.top_level; check_uvars = _84_974.check_uvars; use_eq = _84_974.use_eq; is_iface = _84_974.is_iface; admit = _84_974.admit; default_effects = _84_974.default_effects; type_of = _84_974.type_of; use_bv_sorts = _84_974.use_bv_sorts}))
in (build_lattice _187_933 s)))

let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (let _187_944 = (let _84_979 = env
in (let _187_943 = (let _187_942 = (let _187_941 = (let _187_940 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_187_940, s, us))
in Binding_sig_inst (_187_941))
in (_187_942)::env.gamma)
in {solver = _84_979.solver; range = _84_979.range; curmodule = _84_979.curmodule; gamma = _187_943; gamma_cache = _84_979.gamma_cache; modules = _84_979.modules; expected_typ = _84_979.expected_typ; sigtab = _84_979.sigtab; is_pattern = _84_979.is_pattern; instantiate_imp = _84_979.instantiate_imp; effects = _84_979.effects; generalize = _84_979.generalize; letrecs = _84_979.letrecs; top_level = _84_979.top_level; check_uvars = _84_979.check_uvars; use_eq = _84_979.use_eq; is_iface = _84_979.is_iface; admit = _84_979.admit; default_effects = _84_979.default_effects; type_of = _84_979.type_of; use_bv_sorts = _84_979.use_bv_sorts}))
in (build_lattice _187_944 s)))

let push_local_binding : env  ->  binding  ->  env = (fun env b -> (let _84_983 = env
in {solver = _84_983.solver; range = _84_983.range; curmodule = _84_983.curmodule; gamma = (b)::env.gamma; gamma_cache = _84_983.gamma_cache; modules = _84_983.modules; expected_typ = _84_983.expected_typ; sigtab = _84_983.sigtab; is_pattern = _84_983.is_pattern; instantiate_imp = _84_983.instantiate_imp; effects = _84_983.effects; generalize = _84_983.generalize; letrecs = _84_983.letrecs; top_level = _84_983.top_level; check_uvars = _84_983.check_uvars; use_eq = _84_983.use_eq; is_iface = _84_983.is_iface; admit = _84_983.admit; default_effects = _84_983.default_effects; type_of = _84_983.type_of; use_bv_sorts = _84_983.use_bv_sorts}))

let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))

let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _84_993 -> (match (_84_993) with
| (x, _84_992) -> begin
(push_bv env x)
end)) env bs))

let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(let _84_998 = ()
in (let x = (let _84_1000 = x
in {FStar_Syntax_Syntax.ppname = _84_1000.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _84_1000.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (lid) -> begin
Binding_lid ((lid, t))
end))

let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))

let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (let _84_1010 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (let _84_1012 = env
in {solver = _84_1012.solver; range = _84_1012.range; curmodule = _84_1012.curmodule; gamma = []; gamma_cache = _84_1012.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _84_1012.sigtab; is_pattern = _84_1012.is_pattern; instantiate_imp = _84_1012.instantiate_imp; effects = _84_1012.effects; generalize = _84_1012.generalize; letrecs = _84_1012.letrecs; top_level = _84_1012.top_level; check_uvars = _84_1012.check_uvars; use_eq = _84_1012.use_eq; is_iface = _84_1012.is_iface; admit = _84_1012.admit; default_effects = _84_1012.default_effects; type_of = _84_1012.type_of; use_bv_sorts = _84_1012.use_bv_sorts})))

let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))

let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (let _84_1020 = env
in {solver = _84_1020.solver; range = _84_1020.range; curmodule = _84_1020.curmodule; gamma = _84_1020.gamma; gamma_cache = _84_1020.gamma_cache; modules = _84_1020.modules; expected_typ = Some (t); sigtab = _84_1020.sigtab; is_pattern = _84_1020.is_pattern; instantiate_imp = _84_1020.instantiate_imp; effects = _84_1020.effects; generalize = _84_1020.generalize; letrecs = _84_1020.letrecs; top_level = _84_1020.top_level; check_uvars = _84_1020.check_uvars; use_eq = false; is_iface = _84_1020.is_iface; admit = _84_1020.admit; default_effects = _84_1020.default_effects; type_of = _84_1020.type_of; use_bv_sorts = _84_1020.use_bv_sorts}))

let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _187_987 = (expected_typ env)
in ((let _84_1027 = env
in {solver = _84_1027.solver; range = _84_1027.range; curmodule = _84_1027.curmodule; gamma = _84_1027.gamma; gamma_cache = _84_1027.gamma_cache; modules = _84_1027.modules; expected_typ = None; sigtab = _84_1027.sigtab; is_pattern = _84_1027.is_pattern; instantiate_imp = _84_1027.instantiate_imp; effects = _84_1027.effects; generalize = _84_1027.generalize; letrecs = _84_1027.letrecs; top_level = _84_1027.top_level; check_uvars = _84_1027.check_uvars; use_eq = false; is_iface = _84_1027.is_iface; admit = _84_1027.admit; default_effects = _84_1027.default_effects; type_of = _84_1027.type_of; use_bv_sorts = _84_1027.use_bv_sorts}), _187_987)))

let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(FStar_All.pipe_right env.gamma (FStar_List.collect (fun _84_10 -> (match (_84_10) with
| Binding_sig (_84_1034, se) -> begin
(se)::[]
end
| _84_1039 -> begin
[]
end))))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (let _84_1041 = (add_sigelts env sigs)
in (let _84_1043 = (FStar_Util.smap_clear env.gamma_cache)
in (let _84_1045 = env
in {solver = _84_1045.solver; range = _84_1045.range; curmodule = empty_lid; gamma = []; gamma_cache = _84_1045.gamma_cache; modules = (m)::env.modules; expected_typ = _84_1045.expected_typ; sigtab = _84_1045.sigtab; is_pattern = _84_1045.is_pattern; instantiate_imp = _84_1045.instantiate_imp; effects = _84_1045.effects; generalize = _84_1045.generalize; letrecs = _84_1045.letrecs; top_level = _84_1045.top_level; check_uvars = _84_1045.check_uvars; use_eq = _84_1045.use_eq; is_iface = _84_1045.is_iface; admit = _84_1045.admit; default_effects = _84_1045.default_effects; type_of = _84_1045.type_of; use_bv_sorts = _84_1045.use_bv_sorts}))))))

let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| Binding_univ (_84_1058)::tl -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _187_1004 = (let _187_1003 = (FStar_Syntax_Free.uvars t)
in (ext out _187_1003))
in (aux _187_1004 tl))
end
| (Binding_sig (_)::_) | (Binding_sig_inst (_)::_) -> begin
out
end))
in (aux no_uvs env.gamma)))))

let univ_vars : env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun env -> (let no_univs = FStar_Syntax_Syntax.no_universe_uvars
in (let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_sig_inst (_)::tl) | (Binding_univ (_)::tl) -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _187_1016 = (let _187_1015 = (FStar_Syntax_Free.univs t)
in (ext out _187_1015))
in (aux _187_1016 tl))
end
| Binding_sig (_84_1128)::_84_1126 -> begin
out
end))
in (aux no_univs env.gamma)))))

let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _84_11 -> (match (_84_11) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))

let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _187_1023 = (let _187_1022 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _187_1022 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _187_1023 FStar_List.rev)))

let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))

let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))

let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))

let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (let keys = (FStar_List.fold_left (fun keys _84_12 -> (match (_84_12) with
| Binding_sig (lids, _84_1160) -> begin
(FStar_List.append lids keys)
end
| _84_1164 -> begin
keys
end)) [] env.gamma)
in (let _187_1047 = (sigtab env)
in (FStar_Util.smap_fold _187_1047 (fun _84_1166 v keys -> (let _187_1046 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _187_1046 keys))) keys))))

let dummy_solver : solver_t = {init = (fun _84_1170 -> ()); push = (fun _84_1172 -> ()); pop = (fun _84_1174 -> ()); mark = (fun _84_1176 -> ()); reset_mark = (fun _84_1178 -> ()); commit_mark = (fun _84_1180 -> ()); encode_modul = (fun _84_1182 _84_1184 -> ()); encode_sig = (fun _84_1186 _84_1188 -> ()); solve = (fun _84_1190 _84_1192 -> ()); is_trivial = (fun _84_1194 _84_1196 -> false); finish = (fun _84_1198 -> ()); refresh = (fun _84_1199 -> ())}

let no_solver_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t))  ->  env = (fun tc -> (let _187_1076 = (FStar_Ident.lid_of_path (("dummy")::[]) FStar_Range.dummyRange)
in (initial_env tc dummy_solver _187_1076)))




