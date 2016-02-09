
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
| Binding_var (_83_15) -> begin
_83_15
end))

let ___Binding_lid____0 : binding  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme) = (fun projectee -> (match (projectee) with
| Binding_lid (_83_18) -> begin
_83_18
end))

let ___Binding_sig____0 : binding  ->  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt) = (fun projectee -> (match (projectee) with
| Binding_sig (_83_21) -> begin
_83_21
end))

let ___Binding_univ____0 : binding  ->  FStar_Syntax_Syntax.univ_name = (fun projectee -> (match (projectee) with
| Binding_univ (_83_24) -> begin
_83_24
end))

let ___Binding_sig_inst____0 : binding  ->  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes) = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_83_27) -> begin
_83_27
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
| _83_44 -> begin
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

let new_sigtab = (fun _83_114 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))

let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t))  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun tc solver module_lid -> (let _185_359 = (FStar_Util.smap_create 100)
in (let _185_358 = (let _185_357 = (new_sigtab ())
in (_185_357)::[])
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _185_359; modules = []; expected_typ = None; sigtab = _185_358; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []; type_of = tc; use_bv_sorts = false})))

let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> (FStar_List.hd env.sigtab))

let push : env  ->  Prims.string  ->  env = (fun env msg -> (let _83_121 = (env.solver.push msg)
in (let _83_123 = env
in (let _185_368 = (let _185_367 = (let _185_366 = (sigtab env)
in (FStar_Util.smap_copy _185_366))
in (_185_367)::env.sigtab)
in {solver = _83_123.solver; range = _83_123.range; curmodule = _83_123.curmodule; gamma = _83_123.gamma; gamma_cache = _83_123.gamma_cache; modules = _83_123.modules; expected_typ = _83_123.expected_typ; sigtab = _185_368; is_pattern = _83_123.is_pattern; instantiate_imp = _83_123.instantiate_imp; effects = _83_123.effects; generalize = _83_123.generalize; letrecs = _83_123.letrecs; top_level = _83_123.top_level; check_uvars = _83_123.check_uvars; use_eq = _83_123.use_eq; is_iface = _83_123.is_iface; admit = _83_123.admit; default_effects = _83_123.default_effects; type_of = _83_123.type_of; use_bv_sorts = _83_123.use_bv_sorts}))))

let mark : env  ->  env = (fun env -> (let _83_126 = (env.solver.mark "USER MARK")
in (let _83_128 = env
in (let _185_373 = (let _185_372 = (let _185_371 = (sigtab env)
in (FStar_Util.smap_copy _185_371))
in (_185_372)::env.sigtab)
in {solver = _83_128.solver; range = _83_128.range; curmodule = _83_128.curmodule; gamma = _83_128.gamma; gamma_cache = _83_128.gamma_cache; modules = _83_128.modules; expected_typ = _83_128.expected_typ; sigtab = _185_373; is_pattern = _83_128.is_pattern; instantiate_imp = _83_128.instantiate_imp; effects = _83_128.effects; generalize = _83_128.generalize; letrecs = _83_128.letrecs; top_level = _83_128.top_level; check_uvars = _83_128.check_uvars; use_eq = _83_128.use_eq; is_iface = _83_128.is_iface; admit = _83_128.admit; default_effects = _83_128.default_effects; type_of = _83_128.type_of; use_bv_sorts = _83_128.use_bv_sorts}))))

let commit_mark : env  ->  env = (fun env -> (let _83_131 = (env.solver.commit_mark "USER MARK")
in (let sigtab = (match (env.sigtab) with
| hd::_83_135::tl -> begin
(hd)::tl
end
| _83_140 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _83_142 = env
in {solver = _83_142.solver; range = _83_142.range; curmodule = _83_142.curmodule; gamma = _83_142.gamma; gamma_cache = _83_142.gamma_cache; modules = _83_142.modules; expected_typ = _83_142.expected_typ; sigtab = sigtab; is_pattern = _83_142.is_pattern; instantiate_imp = _83_142.instantiate_imp; effects = _83_142.effects; generalize = _83_142.generalize; letrecs = _83_142.letrecs; top_level = _83_142.top_level; check_uvars = _83_142.check_uvars; use_eq = _83_142.use_eq; is_iface = _83_142.is_iface; admit = _83_142.admit; default_effects = _83_142.default_effects; type_of = _83_142.type_of; use_bv_sorts = _83_142.use_bv_sorts}))))

let reset_mark : env  ->  env = (fun env -> (let _83_145 = (env.solver.reset_mark "USER MARK")
in (let _83_147 = env
in (let _185_378 = (FStar_List.tl env.sigtab)
in {solver = _83_147.solver; range = _83_147.range; curmodule = _83_147.curmodule; gamma = _83_147.gamma; gamma_cache = _83_147.gamma_cache; modules = _83_147.modules; expected_typ = _83_147.expected_typ; sigtab = _185_378; is_pattern = _83_147.is_pattern; instantiate_imp = _83_147.instantiate_imp; effects = _83_147.effects; generalize = _83_147.generalize; letrecs = _83_147.letrecs; top_level = _83_147.top_level; check_uvars = _83_147.check_uvars; use_eq = _83_147.use_eq; is_iface = _83_147.is_iface; admit = _83_147.admit; default_effects = _83_147.default_effects; type_of = _83_147.type_of; use_bv_sorts = _83_147.use_bv_sorts}))))

let pop : env  ->  Prims.string  ->  env = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(FStar_All.failwith "Too many pops")
end
| _83_157::tl -> begin
(let _83_159 = (env.solver.pop msg)
in (let _83_161 = env
in {solver = _83_161.solver; range = _83_161.range; curmodule = _83_161.curmodule; gamma = _83_161.gamma; gamma_cache = _83_161.gamma_cache; modules = _83_161.modules; expected_typ = _83_161.expected_typ; sigtab = tl; is_pattern = _83_161.is_pattern; instantiate_imp = _83_161.instantiate_imp; effects = _83_161.effects; generalize = _83_161.generalize; letrecs = _83_161.letrecs; top_level = _83_161.top_level; check_uvars = _83_161.check_uvars; use_eq = _83_161.use_eq; is_iface = _83_161.is_iface; admit = _83_161.admit; default_effects = _83_161.default_effects; type_of = _83_161.type_of; use_bv_sorts = _83_161.use_bv_sorts}))
end))

let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> ((let _185_388 = (FStar_ST.read FStar_Options.debug)
in (FStar_All.pipe_right _185_388 (FStar_Util.for_some (fun x -> ((env.curmodule.FStar_Ident.str = "") || (env.curmodule.FStar_Ident.str = x)))))) && (FStar_Options.debug_level_geq l)))

let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(let _83_168 = e
in {solver = _83_168.solver; range = r; curmodule = _83_168.curmodule; gamma = _83_168.gamma; gamma_cache = _83_168.gamma_cache; modules = _83_168.modules; expected_typ = _83_168.expected_typ; sigtab = _83_168.sigtab; is_pattern = _83_168.is_pattern; instantiate_imp = _83_168.instantiate_imp; effects = _83_168.effects; generalize = _83_168.generalize; letrecs = _83_168.letrecs; top_level = _83_168.top_level; check_uvars = _83_168.check_uvars; use_eq = _83_168.use_eq; is_iface = _83_168.is_iface; admit = _83_168.admit; default_effects = _83_168.default_effects; type_of = _83_168.type_of; use_bv_sorts = _83_168.use_bv_sorts})
end)

let get_range : env  ->  FStar_Range.range = (fun e -> e.range)

let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)

let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)

let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (let _83_175 = env
in {solver = _83_175.solver; range = _83_175.range; curmodule = lid; gamma = _83_175.gamma; gamma_cache = _83_175.gamma_cache; modules = _83_175.modules; expected_typ = _83_175.expected_typ; sigtab = _83_175.sigtab; is_pattern = _83_175.is_pattern; instantiate_imp = _83_175.instantiate_imp; effects = _83_175.effects; generalize = _83_175.generalize; letrecs = _83_175.letrecs; top_level = _83_175.top_level; check_uvars = _83_175.check_uvars; use_eq = _83_175.use_eq; is_iface = _83_175.is_iface; admit = _83_175.admit; default_effects = _83_175.default_effects; type_of = _83_175.type_of; use_bv_sorts = _83_175.use_bv_sorts}))

let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))

let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (let _185_412 = (sigtab env)
in (FStar_Util.smap_try_find _185_412 (FStar_Ident.text_of_lid lid))))

let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))

let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _185_417 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _185_417)))

let new_u_univ = (fun _83_184 -> (let _185_419 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_185_419)))

let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match ((ts, us)) with
| (([], t), []) -> begin
([], t)
end
| ((formals, t), _83_197) -> begin
(let _83_199 = ()
in (let n = ((FStar_List.length formals) - 1)
in (let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN (((n - i), u)))))
in (let _185_426 = (FStar_Syntax_Subst.subst vs t)
in (us, _185_426)))))
end))

let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _83_1 -> (match (_83_1) with
| ([], t) -> begin
([], t)
end
| (us, t) -> begin
(let us' = (FStar_All.pipe_right us (FStar_List.map (fun _83_212 -> (new_u_univ ()))))
in (inst_tscheme_with (us, t) us'))
end))

let inst_effect_fun : env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun env ed _83_219 -> (match (_83_219) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(let _185_436 = (inst_tscheme ((FStar_List.append ed.FStar_Syntax_Syntax.univs us), t))
in (Prims.snd _185_436))
end
| _83_222 -> begin
(let _185_438 = (let _185_437 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _185_437))
in (FStar_All.failwith _185_438))
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
| ([], _83_233) -> begin
Maybe
end
| (_83_236, []) -> begin
No
end
| (hd::tl, hd'::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _83_247 -> begin
No
end))
in (aux cur lns))))
end else begin
No
end
end))

let lookup_qname : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either Prims.option = (fun env lid -> (let cur_mod = (in_cur_mod env lid)
in (let cache = (fun t -> (let _83_253 = (FStar_Util.smap_add env.gamma_cache lid.FStar_Ident.str t)
in Some (t)))
in (let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find env.gamma_cache lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _83_2 -> (match (_83_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _185_458 = (let _185_457 = (inst_tscheme t)
in FStar_Util.Inl (_185_457))
in Some (_185_458))
end else begin
None
end
end
| Binding_sig (_83_262, FStar_Syntax_Syntax.Sig_bundle (ses, _83_265, _83_267, _83_269)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _185_460 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _185_460 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr ((se, None))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_83_282) -> begin
Some (t)
end
| _83_285 -> begin
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
| _83_292 -> begin
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
| FStar_Syntax_Syntax.Sig_bundle (ses, _83_302, _83_304, _83_306) -> begin
(add_sigelts env ses)
end
| _83_310 -> begin
(let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _185_470 = (sigtab env)
in (FStar_Util.smap_add _185_470 l.FStar_Ident.str se))) lids))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))

let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun _83_3 -> (match (_83_3) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _83_321 -> begin
None
end))))

let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _83_4 -> (match (_83_4) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _83_328 -> begin
false
end)) env.gamma) FStar_Option.isSome))

let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_83_332, lb::[]), _83_337, _83_339, _83_341) -> begin
(let _185_490 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_185_490))
end
| FStar_Syntax_Syntax.Sig_let ((_83_345, lbs), _83_349, _83_351, _83_353) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_83_358) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (lid') -> begin
if (FStar_Ident.lid_equals lid lid') then begin
(let _185_492 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_185_492))
end else begin
None
end
end)))
end
| _83_363 -> begin
None
end))

let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _185_500 = (let _185_499 = (let _185_498 = (variable_not_found bv)
in (let _185_497 = (FStar_Syntax_Syntax.range_of_bv bv)
in (_185_498, _185_497)))
in FStar_Syntax_Syntax.Error (_185_499))
in (Prims.raise _185_500))
end
| Some (t) -> begin
t
end))

let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _83_372) -> begin
(let _185_506 = (let _185_505 = (let _185_504 = (let _185_503 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _185_503))
in (ne.FStar_Syntax_Syntax.univs, _185_504))
in (inst_tscheme _185_505))
in Some (_185_506))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _83_379, _83_381, _83_383) -> begin
(let _185_510 = (let _185_509 = (let _185_508 = (let _185_507 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _185_507))
in (us, _185_508))
in (inst_tscheme _185_509))
in Some (_185_510))
end
| _83_387 -> begin
None
end))

let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_83_397, t) -> begin
Some (t)
end)
end
| _83_402 -> begin
None
end))

let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env lid -> (let mapper = (fun _83_5 -> (match (_83_5) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_83_409, uvs, t, _83_413, _83_415, _83_417, _83_419, _83_421), None) -> begin
(let _185_521 = (inst_tscheme (uvs, t))
in Some (_185_521))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _83_432), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _185_522 = (inst_tscheme (uvs, t))
in Some (_185_522))
end else begin
None
end
end else begin
(let _185_523 = (inst_tscheme (uvs, t))
in Some (_185_523))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _83_443, _83_445, _83_447, _83_449), None) -> begin
(match (tps) with
| [] -> begin
(let _185_525 = (inst_tscheme (uvs, k))
in (FStar_All.pipe_left (fun _185_524 -> Some (_185_524)) _185_525))
end
| _83_457 -> begin
(let _185_530 = (let _185_529 = (let _185_528 = (let _185_527 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _185_527))
in (uvs, _185_528))
in (inst_tscheme _185_529))
in (FStar_All.pipe_left (fun _185_526 -> Some (_185_526)) _185_530))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _83_463, _83_465, _83_467, _83_469), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _185_532 = (inst_tscheme_with (uvs, k) us)
in (FStar_All.pipe_left (fun _185_531 -> Some (_185_531)) _185_532))
end
| _83_478 -> begin
(let _185_537 = (let _185_536 = (let _185_535 = (let _185_534 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _185_534))
in (uvs, _185_535))
in (inst_tscheme_with _185_536 us))
in (FStar_All.pipe_left (fun _185_533 -> Some (_185_533)) _185_537))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_83_482), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _83_487 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _185_538 = (lookup_qname env lid)
in (FStar_Util.bind_opt _185_538 mapper))) with
| Some (us, t) -> begin
Some ((us, (let _83_493 = t
in {FStar_Syntax_Syntax.n = _83_493.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _83_493.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _83_493.FStar_Syntax_Syntax.vars})))
end
| None -> begin
None
end)))

let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _185_545 = (let _185_544 = (let _185_543 = (name_not_found l)
in (_185_543, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_185_544))
in (Prims.raise _185_545))
end
| Some (x) -> begin
x
end))

let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_83_504, uvs, t, _83_508, _83_510), None)) -> begin
(inst_tscheme (uvs, t))
end
| _83_518 -> begin
(let _185_552 = (let _185_551 = (let _185_550 = (name_not_found lid)
in (_185_550, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_185_551))
in (Prims.raise _185_552))
end))

let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_83_522, uvs, t, _83_526, _83_528, _83_530, _83_532, _83_534), None)) -> begin
(inst_tscheme (uvs, t))
end
| _83_542 -> begin
(let _185_559 = (let _185_558 = (let _185_557 = (name_not_found lid)
in (_185_557, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_185_558))
in (Prims.raise _185_559))
end))

let lookup_definition : delta_level  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_83_552, lbs), _83_556, _83_558, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (let lid' = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Ident.lid_equals lid lid') then begin
(let _185_568 = (let _185_567 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (lb.FStar_Syntax_Syntax.lbunivs, _185_567))
in Some (_185_568))
end else begin
None
end)))
end
| _83_565 -> begin
None
end)
end
| _83_567 -> begin
None
end))

let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _185_575 = (let _185_574 = (let _185_573 = (name_not_found ftv)
in (_185_573, (FStar_Ident.range_of_lid ftv)))
in FStar_Syntax_Syntax.Error (_185_574))
in (Prims.raise _185_575))
end
| Some (k) -> begin
k
end))

let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (let fail = (fun _83_577 -> (match (()) with
| () -> begin
(let _185_586 = (let _185_585 = (FStar_Util.string_of_int i)
in (let _185_584 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _185_585 _185_584)))
in (FStar_All.failwith _185_586))
end))
in (let _83_581 = (lookup_datacon env lid)
in (match (_83_581) with
| (_83_579, t) -> begin
(match ((let _185_587 = (FStar_Syntax_Subst.compress t)
in _185_587.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _83_584) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(let b = (FStar_List.nth binders i)
in (let _185_588 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _185_588 Prims.fst)))
end
end
| _83_589 -> begin
(fail ())
end)
end))))

let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_83_593, uvs, t, q, _83_598), None)) -> begin
Some (((uvs, t), q))
end
| _83_606 -> begin
None
end))

let lookup_effect_abbrev : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _83_615), None)) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_6 -> (match (_83_6) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _83_625 -> begin
false
end)))) then begin
None
end else begin
(let _83_630 = (FStar_Syntax_Util.open_univ_vars_binders_and_comp univs binders c)
in (match (_83_630) with
| (_83_627, binders, c) -> begin
Some ((binders, c))
end))
end
end
| _83_632 -> begin
None
end))

let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_83_636, _83_638, _83_640, _83_642, _83_644, dcs, _83_647, _83_649), _83_653)) -> begin
dcs
end
| _83_658 -> begin
[]
end))

let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_83_662, _83_664, _83_666, l, _83_669, _83_671, _83_673, _83_675), _83_679)) -> begin
l
end
| _83_684 -> begin
(let _185_607 = (let _185_606 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _185_606))
in (FStar_All.failwith _185_607))
end))

let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_83_688, _83_690, _83_692, _83_694, _83_696, _83_698, _83_700, _83_702), _83_706)) -> begin
true
end
| _83_711 -> begin
false
end))

let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_83_715, _83_717, _83_719, _83_721, _83_723, _83_725, tags, _83_728), _83_732)) -> begin
(FStar_Util.for_some (fun _83_7 -> (match (_83_7) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _83_744 -> begin
false
end)) tags)
end
| _83_746 -> begin
false
end))

let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_83_750, _83_752, _83_754, quals, _83_757), _83_761)) -> begin
(FStar_Util.for_some (fun _83_8 -> (match (_83_8) with
| FStar_Syntax_Syntax.Projector (_83_767) -> begin
true
end
| _83_770 -> begin
false
end)) quals)
end
| _83_772 -> begin
false
end))

let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))

let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _185_633 = (let _185_632 = (let _185_631 = (name_not_found l)
in (_185_631, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_185_632))
in (Prims.raise _185_633))
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
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _83_800 -> (match (_83_800) with
| (m1, m2, _83_795, _83_797, _83_799) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _185_709 = (let _185_708 = (let _185_707 = (let _185_706 = (FStar_Syntax_Print.lid_to_string l1)
in (let _185_705 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _185_706 _185_705)))
in (_185_707, env.range))
in FStar_Syntax_Syntax.Error (_185_708))
in (Prims.raise _185_709))
end
| Some (_83_803, _83_805, m3, j1, j2) -> begin
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
(let _185_724 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _185_724))
end
| Some (md) -> begin
(let _83_826 = (inst_tscheme (md.FStar_Syntax_Syntax.univs, md.FStar_Syntax_Syntax.signature))
in (match (_83_826) with
| (_83_824, s) -> begin
(let s = (FStar_Syntax_Subst.compress s)
in (match ((md.FStar_Syntax_Syntax.binders, s.FStar_Syntax_Syntax.n)) with
| ([], FStar_Syntax_Syntax.Tm_arrow ((a, _83_839)::(wp, _83_835)::(wlp, _83_831)::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _83_847 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))

let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))

let default_effect : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (FStar_Util.find_map env.default_effects (fun _83_854 -> (match (_83_854) with
| (l', m) -> begin
if (FStar_Ident.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))

let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, _83_859, _83_861, c, quals, r) -> begin
(match ((FStar_Util.find_map quals (fun _83_9 -> (match (_83_9) with
| FStar_Syntax_Syntax.DefaultEffect (n) -> begin
n
end
| _83_871 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(let _83_875 = env
in {solver = _83_875.solver; range = _83_875.range; curmodule = _83_875.curmodule; gamma = _83_875.gamma; gamma_cache = _83_875.gamma_cache; modules = _83_875.modules; expected_typ = _83_875.expected_typ; sigtab = _83_875.sigtab; is_pattern = _83_875.is_pattern; instantiate_imp = _83_875.instantiate_imp; effects = _83_875.effects; generalize = _83_875.generalize; letrecs = _83_875.letrecs; top_level = _83_875.top_level; check_uvars = _83_875.check_uvars; use_eq = _83_875.use_eq; is_iface = _83_875.is_iface; admit = _83_875.admit; default_effects = ((e, l))::env.default_effects; type_of = _83_875.type_of; use_bv_sorts = _83_875.use_bv_sorts})
end)
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _83_879) -> begin
(let effects = (let _83_882 = env.effects
in {decls = (ne)::env.effects.decls; order = _83_882.order; joins = _83_882.joins})
in (let _83_885 = env
in {solver = _83_885.solver; range = _83_885.range; curmodule = _83_885.curmodule; gamma = _83_885.gamma; gamma_cache = _83_885.gamma_cache; modules = _83_885.modules; expected_typ = _83_885.expected_typ; sigtab = _83_885.sigtab; is_pattern = _83_885.is_pattern; instantiate_imp = _83_885.instantiate_imp; effects = effects; generalize = _83_885.generalize; letrecs = _83_885.letrecs; top_level = _83_885.top_level; check_uvars = _83_885.check_uvars; use_eq = _83_885.use_eq; is_iface = _83_885.is_iface; admit = _83_885.admit; default_effects = _83_885.default_effects; type_of = _83_885.type_of; use_bv_sorts = _83_885.use_bv_sorts}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _83_889) -> begin
(let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _185_745 = (e1.mlift r wp1)
in (e2.mlift r _185_745)))})
in (let mk_lift = (fun lift_t r wp1 -> (let _83_904 = (inst_tscheme lift_t)
in (match (_83_904) with
| (_83_902, lift_t) -> begin
(let _185_757 = (let _185_756 = (let _185_755 = (let _185_754 = (FStar_Syntax_Syntax.as_arg r)
in (let _185_753 = (let _185_752 = (FStar_Syntax_Syntax.as_arg wp1)
in (_185_752)::[])
in (_185_754)::_185_753))
in (lift_t, _185_755))
in FStar_Syntax_Syntax.Tm_app (_185_756))
in (FStar_Syntax_Syntax.mk _185_757 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub.FStar_Syntax_Syntax.lift)}
in (let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (let print_mlift = (fun l -> (let arg = (let _185_774 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _185_774 None))
in (let wp = (let _185_775 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _185_775 None))
in (let _185_776 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _185_776)))))
in (let order = (edge)::env.effects.order
in (let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (let find_edge = (fun order _83_921 -> (match (_83_921) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _185_782 -> Some (_185_782)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _185_790 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _185_789 = (find_edge order (i, k))
in (let _185_788 = (find_edge order (k, j))
in (_185_789, _185_788)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _83_933 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _185_790))) order))
in (let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _185_882 = (find_edge order (i, k))
in (let _185_881 = (find_edge order (j, k))
in (_185_882, _185_881)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _83_950, _83_952) -> begin
if ((let _185_883 = (find_edge order (k, ub))
in (FStar_Util.is_some _185_883)) && (not ((let _185_884 = (find_edge order (ub, k))
in (FStar_Util.is_some _185_884))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _83_956 -> begin
bopt
end)) None))
in (match (join_opt) with
| None -> begin
[]
end
| Some (k, e1, e2) -> begin
((i, j, k, e1.mlift, e2.mlift))::[]
end))))))))
in (let effects = (let _83_965 = env.effects
in {decls = _83_965.decls; order = order; joins = joins})
in (let _83_968 = env
in {solver = _83_968.solver; range = _83_968.range; curmodule = _83_968.curmodule; gamma = _83_968.gamma; gamma_cache = _83_968.gamma_cache; modules = _83_968.modules; expected_typ = _83_968.expected_typ; sigtab = _83_968.sigtab; is_pattern = _83_968.is_pattern; instantiate_imp = _83_968.instantiate_imp; effects = effects; generalize = _83_968.generalize; letrecs = _83_968.letrecs; top_level = _83_968.top_level; check_uvars = _83_968.check_uvars; use_eq = _83_968.use_eq; is_iface = _83_968.is_iface; admit = _83_968.admit; default_effects = _83_968.default_effects; type_of = _83_968.type_of; use_bv_sorts = _83_968.use_bv_sorts})))))))))))))
end
| _83_971 -> begin
env
end))

let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (let _185_933 = (let _83_974 = env
in (let _185_932 = (let _185_931 = (let _185_930 = (let _185_929 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_185_929, s))
in Binding_sig (_185_930))
in (_185_931)::env.gamma)
in {solver = _83_974.solver; range = _83_974.range; curmodule = _83_974.curmodule; gamma = _185_932; gamma_cache = _83_974.gamma_cache; modules = _83_974.modules; expected_typ = _83_974.expected_typ; sigtab = _83_974.sigtab; is_pattern = _83_974.is_pattern; instantiate_imp = _83_974.instantiate_imp; effects = _83_974.effects; generalize = _83_974.generalize; letrecs = _83_974.letrecs; top_level = _83_974.top_level; check_uvars = _83_974.check_uvars; use_eq = _83_974.use_eq; is_iface = _83_974.is_iface; admit = _83_974.admit; default_effects = _83_974.default_effects; type_of = _83_974.type_of; use_bv_sorts = _83_974.use_bv_sorts}))
in (build_lattice _185_933 s)))

let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (let _185_944 = (let _83_979 = env
in (let _185_943 = (let _185_942 = (let _185_941 = (let _185_940 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_185_940, s, us))
in Binding_sig_inst (_185_941))
in (_185_942)::env.gamma)
in {solver = _83_979.solver; range = _83_979.range; curmodule = _83_979.curmodule; gamma = _185_943; gamma_cache = _83_979.gamma_cache; modules = _83_979.modules; expected_typ = _83_979.expected_typ; sigtab = _83_979.sigtab; is_pattern = _83_979.is_pattern; instantiate_imp = _83_979.instantiate_imp; effects = _83_979.effects; generalize = _83_979.generalize; letrecs = _83_979.letrecs; top_level = _83_979.top_level; check_uvars = _83_979.check_uvars; use_eq = _83_979.use_eq; is_iface = _83_979.is_iface; admit = _83_979.admit; default_effects = _83_979.default_effects; type_of = _83_979.type_of; use_bv_sorts = _83_979.use_bv_sorts}))
in (build_lattice _185_944 s)))

let push_local_binding : env  ->  binding  ->  env = (fun env b -> (let _83_983 = env
in {solver = _83_983.solver; range = _83_983.range; curmodule = _83_983.curmodule; gamma = (b)::env.gamma; gamma_cache = _83_983.gamma_cache; modules = _83_983.modules; expected_typ = _83_983.expected_typ; sigtab = _83_983.sigtab; is_pattern = _83_983.is_pattern; instantiate_imp = _83_983.instantiate_imp; effects = _83_983.effects; generalize = _83_983.generalize; letrecs = _83_983.letrecs; top_level = _83_983.top_level; check_uvars = _83_983.check_uvars; use_eq = _83_983.use_eq; is_iface = _83_983.is_iface; admit = _83_983.admit; default_effects = _83_983.default_effects; type_of = _83_983.type_of; use_bv_sorts = _83_983.use_bv_sorts}))

let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))

let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _83_993 -> (match (_83_993) with
| (x, _83_992) -> begin
(push_bv env x)
end)) env bs))

let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(let _83_998 = ()
in (let x = (let _83_1000 = x
in {FStar_Syntax_Syntax.ppname = _83_1000.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _83_1000.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (lid) -> begin
Binding_lid ((lid, t))
end))

let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))

let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (let _83_1010 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (let _83_1012 = env
in {solver = _83_1012.solver; range = _83_1012.range; curmodule = _83_1012.curmodule; gamma = []; gamma_cache = _83_1012.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _83_1012.sigtab; is_pattern = _83_1012.is_pattern; instantiate_imp = _83_1012.instantiate_imp; effects = _83_1012.effects; generalize = _83_1012.generalize; letrecs = _83_1012.letrecs; top_level = _83_1012.top_level; check_uvars = _83_1012.check_uvars; use_eq = _83_1012.use_eq; is_iface = _83_1012.is_iface; admit = _83_1012.admit; default_effects = _83_1012.default_effects; type_of = _83_1012.type_of; use_bv_sorts = _83_1012.use_bv_sorts})))

let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))

let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (let _83_1020 = env
in {solver = _83_1020.solver; range = _83_1020.range; curmodule = _83_1020.curmodule; gamma = _83_1020.gamma; gamma_cache = _83_1020.gamma_cache; modules = _83_1020.modules; expected_typ = Some (t); sigtab = _83_1020.sigtab; is_pattern = _83_1020.is_pattern; instantiate_imp = _83_1020.instantiate_imp; effects = _83_1020.effects; generalize = _83_1020.generalize; letrecs = _83_1020.letrecs; top_level = _83_1020.top_level; check_uvars = _83_1020.check_uvars; use_eq = false; is_iface = _83_1020.is_iface; admit = _83_1020.admit; default_effects = _83_1020.default_effects; type_of = _83_1020.type_of; use_bv_sorts = _83_1020.use_bv_sorts}))

let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _185_987 = (expected_typ env)
in ((let _83_1027 = env
in {solver = _83_1027.solver; range = _83_1027.range; curmodule = _83_1027.curmodule; gamma = _83_1027.gamma; gamma_cache = _83_1027.gamma_cache; modules = _83_1027.modules; expected_typ = None; sigtab = _83_1027.sigtab; is_pattern = _83_1027.is_pattern; instantiate_imp = _83_1027.instantiate_imp; effects = _83_1027.effects; generalize = _83_1027.generalize; letrecs = _83_1027.letrecs; top_level = _83_1027.top_level; check_uvars = _83_1027.check_uvars; use_eq = false; is_iface = _83_1027.is_iface; admit = _83_1027.admit; default_effects = _83_1027.default_effects; type_of = _83_1027.type_of; use_bv_sorts = _83_1027.use_bv_sorts}), _185_987)))

let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(FStar_All.pipe_right env.gamma (FStar_List.collect (fun _83_10 -> (match (_83_10) with
| Binding_sig (_83_1034, se) -> begin
(se)::[]
end
| _83_1039 -> begin
[]
end))))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (let _83_1041 = (add_sigelts env sigs)
in (let _83_1043 = (FStar_Util.smap_clear env.gamma_cache)
in (let _83_1045 = env
in {solver = _83_1045.solver; range = _83_1045.range; curmodule = empty_lid; gamma = []; gamma_cache = _83_1045.gamma_cache; modules = (m)::env.modules; expected_typ = _83_1045.expected_typ; sigtab = _83_1045.sigtab; is_pattern = _83_1045.is_pattern; instantiate_imp = _83_1045.instantiate_imp; effects = _83_1045.effects; generalize = _83_1045.generalize; letrecs = _83_1045.letrecs; top_level = _83_1045.top_level; check_uvars = _83_1045.check_uvars; use_eq = _83_1045.use_eq; is_iface = _83_1045.is_iface; admit = _83_1045.admit; default_effects = _83_1045.default_effects; type_of = _83_1045.type_of; use_bv_sorts = _83_1045.use_bv_sorts}))))))

let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| Binding_univ (_83_1058)::tl -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _185_1004 = (let _185_1003 = (FStar_Syntax_Free.uvars t)
in (ext out _185_1003))
in (aux _185_1004 tl))
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
(let _185_1016 = (let _185_1015 = (FStar_Syntax_Free.univs t)
in (ext out _185_1015))
in (aux _185_1016 tl))
end
| Binding_sig (_83_1128)::_83_1126 -> begin
out
end))
in (aux no_univs env.gamma)))))

let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _83_11 -> (match (_83_11) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))

let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _185_1023 = (let _185_1022 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _185_1022 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _185_1023 FStar_List.rev)))

let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))

let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))

let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))

let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (let keys = (FStar_List.fold_left (fun keys _83_12 -> (match (_83_12) with
| Binding_sig (lids, _83_1160) -> begin
(FStar_List.append lids keys)
end
| _83_1164 -> begin
keys
end)) [] env.gamma)
in (let _185_1047 = (sigtab env)
in (FStar_Util.smap_fold _185_1047 (fun _83_1166 v keys -> (let _185_1046 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _185_1046 keys))) keys))))

let dummy_solver : solver_t = {init = (fun _83_1170 -> ()); push = (fun _83_1172 -> ()); pop = (fun _83_1174 -> ()); mark = (fun _83_1176 -> ()); reset_mark = (fun _83_1178 -> ()); commit_mark = (fun _83_1180 -> ()); encode_modul = (fun _83_1182 _83_1184 -> ()); encode_sig = (fun _83_1186 _83_1188 -> ()); solve = (fun _83_1190 _83_1192 -> ()); is_trivial = (fun _83_1194 _83_1196 -> false); finish = (fun _83_1198 -> ()); refresh = (fun _83_1199 -> ())}

let no_solver_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t))  ->  env = (fun tc -> (let _185_1076 = (FStar_Ident.lid_of_path (("dummy")::[]) FStar_Range.dummyRange)
in (initial_env tc dummy_solver _185_1076)))




