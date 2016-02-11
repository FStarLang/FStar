
open Prims
# 30 "env.fs"
type binding =
| Binding_var of FStar_Syntax_Syntax.bv
| Binding_lid of (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme)
| Binding_sig of (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
| Binding_univ of FStar_Syntax_Syntax.univ_name
| Binding_sig_inst of (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes)

# 31 "env.fs"
let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

# 32 "env.fs"
let is_Binding_lid = (fun _discr_ -> (match (_discr_) with
| Binding_lid (_) -> begin
true
end
| _ -> begin
false
end))

# 33 "env.fs"
let is_Binding_sig = (fun _discr_ -> (match (_discr_) with
| Binding_sig (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "env.fs"
let is_Binding_univ = (fun _discr_ -> (match (_discr_) with
| Binding_univ (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "env.fs"
let is_Binding_sig_inst = (fun _discr_ -> (match (_discr_) with
| Binding_sig_inst (_) -> begin
true
end
| _ -> begin
false
end))

# 31 "env.fs"
let ___Binding_var____0 : binding  ->  FStar_Syntax_Syntax.bv = (fun projectee -> (match (projectee) with
| Binding_var (_83_15) -> begin
_83_15
end))

# 32 "env.fs"
let ___Binding_lid____0 : binding  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme) = (fun projectee -> (match (projectee) with
| Binding_lid (_83_18) -> begin
_83_18
end))

# 33 "env.fs"
let ___Binding_sig____0 : binding  ->  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt) = (fun projectee -> (match (projectee) with
| Binding_sig (_83_21) -> begin
_83_21
end))

# 34 "env.fs"
let ___Binding_univ____0 : binding  ->  FStar_Syntax_Syntax.univ_name = (fun projectee -> (match (projectee) with
| Binding_univ (_83_24) -> begin
_83_24
end))

# 35 "env.fs"
let ___Binding_sig_inst____0 : binding  ->  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes) = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_83_27) -> begin
_83_27
end))

# 37 "env.fs"
type delta_level =
| NoDelta
| OnlyInline
| Unfold

# 38 "env.fs"
let is_NoDelta = (fun _discr_ -> (match (_discr_) with
| NoDelta (_) -> begin
true
end
| _ -> begin
false
end))

# 39 "env.fs"
let is_OnlyInline = (fun _discr_ -> (match (_discr_) with
| OnlyInline (_) -> begin
true
end
| _ -> begin
false
end))

# 40 "env.fs"
let is_Unfold = (fun _discr_ -> (match (_discr_) with
| Unfold (_) -> begin
true
end
| _ -> begin
false
end))

# 42 "env.fs"
let visible_at : delta_level  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun d q -> (match ((d, q)) with
| ((NoDelta, _)) | ((OnlyInline, FStar_Syntax_Syntax.Inline)) | ((Unfold, FStar_Syntax_Syntax.Inline)) | ((Unfold, FStar_Syntax_Syntax.Unfoldable)) -> begin
true
end
| _83_44 -> begin
false
end))

# 49 "env.fs"
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

# 56 "env.fs"
type mlift =
FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ

# 58 "env.fs"
type edge =
{msource : FStar_Ident.lident; mtarget : FStar_Ident.lident; mlift : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ}

# 58 "env.fs"
let is_Mkedge : edge  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkedge"))))

# 63 "env.fs"
type effects =
{decls : FStar_Syntax_Syntax.eff_decl Prims.list; order : edge Prims.list; joins : (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list}

# 63 "env.fs"
let is_Mkeffects : effects  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeffects"))))

# 68 "env.fs"
type cached_elt =
((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either

# 69 "env.fs"
type env =
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ Prims.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap Prims.list; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; default_effects : (FStar_Ident.lident * FStar_Ident.lident) Prims.list; type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t); use_bv_sorts : Prims.bool} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit; solve : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit} 
 and guard_t =
{guard_f : FStar_TypeChecker_Common.guard_formula; deferred : FStar_TypeChecker_Common.deferred; univ_ineqs : FStar_TypeChecker_Common.univ_ineq Prims.list; implicits : (env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list}

# 69 "env.fs"
let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

# 92 "env.fs"
let is_Mksolver_t : solver_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksolver_t"))))

# 106 "env.fs"
let is_Mkguard_t : guard_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkguard_t"))))

# 112 "env.fs"
type env_t =
env

# 113 "env.fs"
type implicits =
(env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list

# 115 "env.fs"
type sigtable =
FStar_Syntax_Syntax.sigelt FStar_Util.smap

# 116 "env.fs"
let default_table_size : Prims.int = 200

# 117 "env.fs"
let new_sigtab = (fun _83_114 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))

# 119 "env.fs"
let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t))  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun tc solver module_lid -> (let _185_359 = (FStar_Util.smap_create 100)
in (let _185_358 = (let _185_357 = (new_sigtab ())
in (_185_357)::[])
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _185_359; modules = []; expected_typ = None; sigtab = _185_358; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []; type_of = tc; use_bv_sorts = false})))

# 144 "env.fs"
let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> (FStar_List.hd env.sigtab))

# 145 "env.fs"
let push : env  ->  Prims.string  ->  env = (fun env msg -> (
# 146 "env.fs"
let _83_121 = (env.solver.push msg)
in (
# 147 "env.fs"
let _83_123 = env
in (let _185_368 = (let _185_367 = (let _185_366 = (sigtab env)
in (FStar_Util.smap_copy _185_366))
in (_185_367)::env.sigtab)
in {solver = _83_123.solver; range = _83_123.range; curmodule = _83_123.curmodule; gamma = _83_123.gamma; gamma_cache = _83_123.gamma_cache; modules = _83_123.modules; expected_typ = _83_123.expected_typ; sigtab = _185_368; is_pattern = _83_123.is_pattern; instantiate_imp = _83_123.instantiate_imp; effects = _83_123.effects; generalize = _83_123.generalize; letrecs = _83_123.letrecs; top_level = _83_123.top_level; check_uvars = _83_123.check_uvars; use_eq = _83_123.use_eq; is_iface = _83_123.is_iface; admit = _83_123.admit; default_effects = _83_123.default_effects; type_of = _83_123.type_of; use_bv_sorts = _83_123.use_bv_sorts}))))

# 148 "env.fs"
let mark : env  ->  env = (fun env -> (
# 149 "env.fs"
let _83_126 = (env.solver.mark "USER MARK")
in (
# 150 "env.fs"
let _83_128 = env
in (let _185_373 = (let _185_372 = (let _185_371 = (sigtab env)
in (FStar_Util.smap_copy _185_371))
in (_185_372)::env.sigtab)
in {solver = _83_128.solver; range = _83_128.range; curmodule = _83_128.curmodule; gamma = _83_128.gamma; gamma_cache = _83_128.gamma_cache; modules = _83_128.modules; expected_typ = _83_128.expected_typ; sigtab = _185_373; is_pattern = _83_128.is_pattern; instantiate_imp = _83_128.instantiate_imp; effects = _83_128.effects; generalize = _83_128.generalize; letrecs = _83_128.letrecs; top_level = _83_128.top_level; check_uvars = _83_128.check_uvars; use_eq = _83_128.use_eq; is_iface = _83_128.is_iface; admit = _83_128.admit; default_effects = _83_128.default_effects; type_of = _83_128.type_of; use_bv_sorts = _83_128.use_bv_sorts}))))

# 151 "env.fs"
let commit_mark : env  ->  env = (fun env -> (
# 152 "env.fs"
let _83_131 = (env.solver.commit_mark "USER MARK")
in (
# 153 "env.fs"
let sigtab = (match (env.sigtab) with
| hd::_83_135::tl -> begin
(hd)::tl
end
| _83_140 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 156 "env.fs"
let _83_142 = env
in {solver = _83_142.solver; range = _83_142.range; curmodule = _83_142.curmodule; gamma = _83_142.gamma; gamma_cache = _83_142.gamma_cache; modules = _83_142.modules; expected_typ = _83_142.expected_typ; sigtab = sigtab; is_pattern = _83_142.is_pattern; instantiate_imp = _83_142.instantiate_imp; effects = _83_142.effects; generalize = _83_142.generalize; letrecs = _83_142.letrecs; top_level = _83_142.top_level; check_uvars = _83_142.check_uvars; use_eq = _83_142.use_eq; is_iface = _83_142.is_iface; admit = _83_142.admit; default_effects = _83_142.default_effects; type_of = _83_142.type_of; use_bv_sorts = _83_142.use_bv_sorts}))))

# 157 "env.fs"
let reset_mark : env  ->  env = (fun env -> (
# 158 "env.fs"
let _83_145 = (env.solver.reset_mark "USER MARK")
in (
# 159 "env.fs"
let _83_147 = env
in (let _185_378 = (FStar_List.tl env.sigtab)
in {solver = _83_147.solver; range = _83_147.range; curmodule = _83_147.curmodule; gamma = _83_147.gamma; gamma_cache = _83_147.gamma_cache; modules = _83_147.modules; expected_typ = _83_147.expected_typ; sigtab = _185_378; is_pattern = _83_147.is_pattern; instantiate_imp = _83_147.instantiate_imp; effects = _83_147.effects; generalize = _83_147.generalize; letrecs = _83_147.letrecs; top_level = _83_147.top_level; check_uvars = _83_147.check_uvars; use_eq = _83_147.use_eq; is_iface = _83_147.is_iface; admit = _83_147.admit; default_effects = _83_147.default_effects; type_of = _83_147.type_of; use_bv_sorts = _83_147.use_bv_sorts}))))

# 160 "env.fs"
let pop : env  ->  Prims.string  ->  env = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(FStar_All.failwith "Too many pops")
end
| _83_157::tl -> begin
(
# 164 "env.fs"
let _83_159 = (env.solver.pop msg)
in (
# 165 "env.fs"
let _83_161 = env
in {solver = _83_161.solver; range = _83_161.range; curmodule = _83_161.curmodule; gamma = _83_161.gamma; gamma_cache = _83_161.gamma_cache; modules = _83_161.modules; expected_typ = _83_161.expected_typ; sigtab = tl; is_pattern = _83_161.is_pattern; instantiate_imp = _83_161.instantiate_imp; effects = _83_161.effects; generalize = _83_161.generalize; letrecs = _83_161.letrecs; top_level = _83_161.top_level; check_uvars = _83_161.check_uvars; use_eq = _83_161.use_eq; is_iface = _83_161.is_iface; admit = _83_161.admit; default_effects = _83_161.default_effects; type_of = _83_161.type_of; use_bv_sorts = _83_161.use_bv_sorts}))
end))

# 170 "env.fs"
let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> ((let _185_388 = (FStar_ST.read FStar_Options.debug)
in (FStar_All.pipe_right _185_388 (FStar_Util.for_some (fun x -> ((env.curmodule.FStar_Ident.str = "") || (env.curmodule.FStar_Ident.str = x)))))) && (FStar_Options.debug_level_geq l)))

# 173 "env.fs"
let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(
# 173 "env.fs"
let _83_168 = e
in {solver = _83_168.solver; range = r; curmodule = _83_168.curmodule; gamma = _83_168.gamma; gamma_cache = _83_168.gamma_cache; modules = _83_168.modules; expected_typ = _83_168.expected_typ; sigtab = _83_168.sigtab; is_pattern = _83_168.is_pattern; instantiate_imp = _83_168.instantiate_imp; effects = _83_168.effects; generalize = _83_168.generalize; letrecs = _83_168.letrecs; top_level = _83_168.top_level; check_uvars = _83_168.check_uvars; use_eq = _83_168.use_eq; is_iface = _83_168.is_iface; admit = _83_168.admit; default_effects = _83_168.default_effects; type_of = _83_168.type_of; use_bv_sorts = _83_168.use_bv_sorts})
end)

# 174 "env.fs"
let get_range : env  ->  FStar_Range.range = (fun e -> e.range)

# 179 "env.fs"
let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)

# 180 "env.fs"
let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)

# 181 "env.fs"
let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (
# 181 "env.fs"
let _83_175 = env
in {solver = _83_175.solver; range = _83_175.range; curmodule = lid; gamma = _83_175.gamma; gamma_cache = _83_175.gamma_cache; modules = _83_175.modules; expected_typ = _83_175.expected_typ; sigtab = _83_175.sigtab; is_pattern = _83_175.is_pattern; instantiate_imp = _83_175.instantiate_imp; effects = _83_175.effects; generalize = _83_175.generalize; letrecs = _83_175.letrecs; top_level = _83_175.top_level; check_uvars = _83_175.check_uvars; use_eq = _83_175.use_eq; is_iface = _83_175.is_iface; admit = _83_175.admit; default_effects = _83_175.default_effects; type_of = _83_175.type_of; use_bv_sorts = _83_175.use_bv_sorts}))

# 182 "env.fs"
let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))

# 183 "env.fs"
let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (let _185_412 = (sigtab env)
in (FStar_Util.smap_try_find _185_412 (FStar_Ident.text_of_lid lid))))

# 185 "env.fs"
let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))

# 188 "env.fs"
let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _185_417 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _185_417)))

# 192 "env.fs"
let new_u_univ = (fun _83_184 -> (let _185_419 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_185_419)))

# 195 "env.fs"
let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match ((ts, us)) with
| (([], t), []) -> begin
([], t)
end
| ((formals, t), _83_197) -> begin
(
# 199 "env.fs"
let _83_199 = ()
in (
# 200 "env.fs"
let n = ((FStar_List.length formals) - 1)
in (
# 201 "env.fs"
let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN (((n - i), u)))))
in (let _185_426 = (FStar_Syntax_Subst.subst vs t)
in (us, _185_426)))))
end))

# 205 "env.fs"
let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _83_1 -> (match (_83_1) with
| ([], t) -> begin
([], t)
end
| (us, t) -> begin
(
# 208 "env.fs"
let us' = (FStar_All.pipe_right us (FStar_List.map (fun _83_212 -> (new_u_univ ()))))
in (inst_tscheme_with (us, t) us'))
end))

# 211 "env.fs"
let inst_effect_fun : env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Ident.ident Prims.list * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.term = (fun env ed _83_219 -> (match (_83_219) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(let _185_436 = (inst_tscheme ((FStar_List.append ed.FStar_Syntax_Syntax.univs us), t))
in (Prims.snd _185_436))
end
| _83_222 -> begin
(let _185_437 = (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname))
in (FStar_All.failwith _185_437))
end)
end))

# 216 "env.fs"
type tri =
| Yes
| No
| Maybe

# 217 "env.fs"
let is_Yes = (fun _discr_ -> (match (_discr_) with
| Yes (_) -> begin
true
end
| _ -> begin
false
end))

# 218 "env.fs"
let is_No = (fun _discr_ -> (match (_discr_) with
| No (_) -> begin
true
end
| _ -> begin
false
end))

# 219 "env.fs"
let is_Maybe = (fun _discr_ -> (match (_discr_) with
| Maybe (_) -> begin
true
end
| _ -> begin
false
end))

# 221 "env.fs"
let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (
# 222 "env.fs"
let cur = (current_module env)
in if (l.FStar_Ident.nsstr = cur.FStar_Ident.str) then begin
Yes
end else begin
if (FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str) then begin
(
# 225 "env.fs"
let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (
# 226 "env.fs"
let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (
# 227 "env.fs"
let rec aux = (fun c l -> (match ((c, l)) with
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

# 235 "env.fs"
let lookup_qname : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either Prims.option = (fun env lid -> (
# 236 "env.fs"
let cur_mod = (in_cur_mod env lid)
in (
# 237 "env.fs"
let cache = (fun t -> (
# 237 "env.fs"
let _83_253 = (FStar_Util.smap_add env.gamma_cache lid.FStar_Ident.str t)
in Some (t)))
in (
# 238 "env.fs"
let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find env.gamma_cache lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _83_2 -> (match (_83_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _185_457 = (let _185_456 = (inst_tscheme t)
in FStar_Util.Inl (_185_456))
in Some (_185_457))
end else begin
None
end
end
| Binding_sig (_83_262, FStar_Syntax_Syntax.Sig_bundle (ses, _83_265, _83_267, _83_269)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _185_459 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _185_459 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr ((se, None))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(
# 249 "env.fs"
let maybe_cache = (fun t -> (match (s) with
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

# 266 "env.fs"
let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _83_302, _83_304, _83_306) -> begin
(add_sigelts env ses)
end
| _83_310 -> begin
(
# 269 "env.fs"
let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _185_469 = (sigtab env)
in (FStar_Util.smap_add _185_469 l.FStar_Ident.str se))) lids))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))

# 278 "env.fs"
let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun _83_3 -> (match (_83_3) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _83_321 -> begin
None
end))))

# 284 "env.fs"
let lookup_univ : env  ->  FStar_Ident.ident  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _83_4 -> (match (_83_4) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _83_328 -> begin
false
end)) env.gamma) FStar_Option.isSome))

# 290 "env.fs"
let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_83_332, lb::[]), _83_337, _83_339, _83_341) -> begin
(let _185_489 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_185_489))
end
| FStar_Syntax_Syntax.Sig_let ((_83_345, lbs), _83_349, _83_351, _83_353) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_83_358) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (lid') -> begin
if (FStar_Ident.lid_equals lid lid') then begin
(let _185_491 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_185_491))
end else begin
None
end
end)))
end
| _83_363 -> begin
None
end))

# 304 "env.fs"
let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _185_498 = (let _185_497 = (let _185_496 = (variable_not_found bv)
in (_185_496, (FStar_Syntax_Syntax.range_of_bv bv)))
in FStar_Syntax_Syntax.Error (_185_497))
in (Prims.raise _185_498))
end
| Some (t) -> begin
t
end))

# 309 "env.fs"
let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _83_372) -> begin
(let _185_504 = (let _185_503 = (let _185_502 = (let _185_501 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _185_501))
in (ne.FStar_Syntax_Syntax.univs, _185_502))
in (inst_tscheme _185_503))
in Some (_185_504))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _83_379, _83_381, _83_383) -> begin
(let _185_508 = (let _185_507 = (let _185_506 = (let _185_505 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _185_505))
in (us, _185_506))
in (inst_tscheme _185_507))
in Some (_185_508))
end
| _83_387 -> begin
None
end))

# 319 "env.fs"
let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
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

# 328 "env.fs"
let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) Prims.option = (fun env lid -> (
# 329 "env.fs"
let mapper = (fun _83_5 -> (match (_83_5) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_83_409, uvs, t, _83_413, _83_415, _83_417, _83_419, _83_421), None) -> begin
(let _185_519 = (inst_tscheme (uvs, t))
in Some (_185_519))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _83_432), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _185_520 = (inst_tscheme (uvs, t))
in Some (_185_520))
end else begin
None
end
end else begin
(let _185_521 = (inst_tscheme (uvs, t))
in Some (_185_521))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _83_443, _83_445, _83_447, _83_449), None) -> begin
(match (tps) with
| [] -> begin
(let _185_523 = (inst_tscheme (uvs, k))
in (FStar_All.pipe_left (fun _185_522 -> Some (_185_522)) _185_523))
end
| _83_457 -> begin
(let _185_528 = (let _185_527 = (let _185_526 = (let _185_525 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _185_525))
in (uvs, _185_526))
in (inst_tscheme _185_527))
in (FStar_All.pipe_left (fun _185_524 -> Some (_185_524)) _185_528))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _83_463, _83_465, _83_467, _83_469), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _185_530 = (inst_tscheme_with (uvs, k) us)
in (FStar_All.pipe_left (fun _185_529 -> Some (_185_529)) _185_530))
end
| _83_478 -> begin
(let _185_535 = (let _185_534 = (let _185_533 = (let _185_532 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _185_532))
in (uvs, _185_533))
in (inst_tscheme_with _185_534 us))
in (FStar_All.pipe_left (fun _185_531 -> Some (_185_531)) _185_535))
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
in (match ((let _185_536 = (lookup_qname env lid)
in (FStar_Util.bind_opt _185_536 mapper))) with
| Some (us, t) -> begin
Some ((us, (
# 363 "env.fs"
let _83_493 = t
in {FStar_Syntax_Syntax.n = _83_493.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _83_493.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _83_493.FStar_Syntax_Syntax.vars})))
end
| None -> begin
None
end)))

# 366 "env.fs"
let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _185_543 = (let _185_542 = (let _185_541 = (name_not_found l)
in (_185_541, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_185_542))
in (Prims.raise _185_543))
end
| Some (x) -> begin
x
end))

# 371 "env.fs"
let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_83_504, uvs, t, _83_508, _83_510), None)) -> begin
(inst_tscheme (uvs, t))
end
| _83_518 -> begin
(let _185_550 = (let _185_549 = (let _185_548 = (name_not_found lid)
in (_185_548, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_185_549))
in (Prims.raise _185_550))
end))

# 376 "env.fs"
let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_83_522, uvs, t, _83_526, _83_528, _83_530, _83_532, _83_534), None)) -> begin
(inst_tscheme (uvs, t))
end
| _83_542 -> begin
(let _185_557 = (let _185_556 = (let _185_555 = (name_not_found lid)
in (_185_555, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_185_556))
in (Prims.raise _185_557))
end))

# 381 "env.fs"
let lookup_definition : delta_level  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_name Prims.list * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) Prims.option = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_83_552, lbs), _83_556, _83_558, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (
# 387 "env.fs"
let lid' = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Ident.lid_equals lid lid') then begin
(let _185_566 = (let _185_565 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (lb.FStar_Syntax_Syntax.lbunivs, _185_565))
in Some (_185_566))
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

# 395 "env.fs"
let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _185_573 = (let _185_572 = (let _185_571 = (name_not_found ftv)
in (_185_571, (FStar_Ident.range_of_lid ftv)))
in FStar_Syntax_Syntax.Error (_185_572))
in (Prims.raise _185_573))
end
| Some (k) -> begin
k
end))

# 400 "env.fs"
let lookup_projector : env  ->  FStar_Ident.lid  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (
# 401 "env.fs"
let fail = (fun _83_577 -> (match (()) with
| () -> begin
(let _185_583 = (let _185_582 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _185_582 (FStar_Syntax_Print.lid_to_string lid)))
in (FStar_All.failwith _185_583))
end))
in (
# 402 "env.fs"
let _83_581 = (lookup_datacon env lid)
in (match (_83_581) with
| (_83_579, t) -> begin
(match ((let _185_584 = (FStar_Syntax_Subst.compress t)
in _185_584.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _83_584) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(
# 407 "env.fs"
let b = (FStar_List.nth binders i)
in (let _185_585 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _185_585 Prims.fst)))
end
end
| _83_589 -> begin
(fail ())
end)
end))))

# 411 "env.fs"
let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_83_593, uvs, t, q, _83_598), None)) -> begin
Some (((uvs, t), q))
end
| _83_606 -> begin
None
end))

# 416 "env.fs"
let lookup_effect_abbrev : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
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
(
# 421 "env.fs"
let _83_630 = (FStar_Syntax_Util.open_univ_vars_binders_and_comp univs binders c)
in (match (_83_630) with
| (_83_627, binders, c) -> begin
Some ((binders, c))
end))
end
end
| _83_632 -> begin
None
end))

# 425 "env.fs"
let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_83_636, _83_638, _83_640, _83_642, _83_644, dcs, _83_647, _83_649), _83_653)) -> begin
dcs
end
| _83_658 -> begin
[]
end))

# 430 "env.fs"
let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_83_662, _83_664, _83_666, l, _83_669, _83_671, _83_673, _83_675), _83_679)) -> begin
l
end
| _83_684 -> begin
(let _185_603 = (FStar_Util.format1 "Not a datacon: %s" (FStar_Syntax_Print.lid_to_string lid))
in (FStar_All.failwith _185_603))
end))

# 435 "env.fs"
let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_83_688, _83_690, _83_692, _83_694, _83_696, _83_698, _83_700, _83_702), _83_706)) -> begin
true
end
| _83_711 -> begin
false
end))

# 440 "env.fs"
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

# 446 "env.fs"
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

# 455 "env.fs"
let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))

# 458 "env.fs"
let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _185_629 = (let _185_628 = (let _185_627 = (name_not_found l)
in (_185_627, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_185_628))
in (Prims.raise _185_629))
end
| Some (md) -> begin
md
end))

# 463 "env.fs"
let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ)) = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
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
(let _185_727 = (let _185_726 = (let _185_725 = (FStar_Util.format2 "Effects %s and %s cannot be composed" (FStar_Syntax_Print.lid_to_string l1) (FStar_Syntax_Print.lid_to_string l2))
in (_185_725, env.range))
in FStar_Syntax_Syntax.Error (_185_726))
in (Prims.raise _185_727))
end
| Some (_83_803, _83_805, m3, j1, j2) -> begin
(m3, j1, j2)
end)
end
end)

# 473 "env.fs"
let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge Prims.option = (fun env l1 l2 -> if ((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid))) then begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end else begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end)

# 479 "env.fs"
let wp_sig_aux : FStar_Syntax_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun decls m -> (match ((FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))))) with
| None -> begin
(let _185_742 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _185_742))
end
| Some (md) -> begin
(
# 483 "env.fs"
let _83_826 = (inst_tscheme (md.FStar_Syntax_Syntax.univs, md.FStar_Syntax_Syntax.signature))
in (match (_83_826) with
| (_83_824, s) -> begin
(
# 484 "env.fs"
let s = (FStar_Syntax_Subst.compress s)
in (match ((md.FStar_Syntax_Syntax.binders, s.FStar_Syntax_Syntax.n)) with
| ([], FStar_Syntax_Syntax.Tm_arrow ((a, _83_839)::(wp, _83_835)::(wlp, _83_831)::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _83_847 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))

# 489 "env.fs"
let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))

# 491 "env.fs"
let default_effect : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (FStar_Util.find_map env.default_effects (fun _83_854 -> (match (_83_854) with
| (l', m) -> begin
if (FStar_Ident.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))

# 493 "env.fs"
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
(
# 497 "env.fs"
let _83_875 = env
in {solver = _83_875.solver; range = _83_875.range; curmodule = _83_875.curmodule; gamma = _83_875.gamma; gamma_cache = _83_875.gamma_cache; modules = _83_875.modules; expected_typ = _83_875.expected_typ; sigtab = _83_875.sigtab; is_pattern = _83_875.is_pattern; instantiate_imp = _83_875.instantiate_imp; effects = _83_875.effects; generalize = _83_875.generalize; letrecs = _83_875.letrecs; top_level = _83_875.top_level; check_uvars = _83_875.check_uvars; use_eq = _83_875.use_eq; is_iface = _83_875.is_iface; admit = _83_875.admit; default_effects = ((e, l))::env.default_effects; type_of = _83_875.type_of; use_bv_sorts = _83_875.use_bv_sorts})
end)
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _83_879) -> begin
(
# 500 "env.fs"
let effects = (
# 500 "env.fs"
let _83_882 = env.effects
in {decls = (ne)::env.effects.decls; order = _83_882.order; joins = _83_882.joins})
in (
# 501 "env.fs"
let _83_885 = env
in {solver = _83_885.solver; range = _83_885.range; curmodule = _83_885.curmodule; gamma = _83_885.gamma; gamma_cache = _83_885.gamma_cache; modules = _83_885.modules; expected_typ = _83_885.expected_typ; sigtab = _83_885.sigtab; is_pattern = _83_885.is_pattern; instantiate_imp = _83_885.instantiate_imp; effects = effects; generalize = _83_885.generalize; letrecs = _83_885.letrecs; top_level = _83_885.top_level; check_uvars = _83_885.check_uvars; use_eq = _83_885.use_eq; is_iface = _83_885.is_iface; admit = _83_885.admit; default_effects = _83_885.default_effects; type_of = _83_885.type_of; use_bv_sorts = _83_885.use_bv_sorts}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _83_889) -> begin
(
# 504 "env.fs"
let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _185_763 = (e1.mlift r wp1)
in (e2.mlift r _185_763)))})
in (
# 509 "env.fs"
let mk_lift = (fun lift_t r wp1 -> (
# 510 "env.fs"
let _83_904 = (inst_tscheme lift_t)
in (match (_83_904) with
| (_83_902, lift_t) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((lift_t, ((FStar_Syntax_Syntax.as_arg r))::((FStar_Syntax_Syntax.as_arg wp1))::[]))) None wp1.FStar_Syntax_Syntax.pos)
end)))
in (
# 513 "env.fs"
let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub.FStar_Syntax_Syntax.lift)}
in (
# 517 "env.fs"
let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (
# 522 "env.fs"
let print_mlift = (fun l -> (
# 523 "env.fs"
let arg = (let _185_786 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _185_786 None))
in (
# 524 "env.fs"
let wp = (let _185_787 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _185_787 None))
in (let _185_788 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _185_788)))))
in (
# 526 "env.fs"
let order = (edge)::env.effects.order
in (
# 528 "env.fs"
let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (
# 530 "env.fs"
let find_edge = (fun order _83_921 -> (match (_83_921) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _185_794 -> Some (_185_794)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (
# 539 "env.fs"
let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _185_802 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _185_801 = (find_edge order (i, k))
in (let _185_800 = (find_edge order (k, j))
in (_185_801, _185_800)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _83_933 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _185_802))) order))
in (
# 550 "env.fs"
let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (
# 552 "env.fs"
let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (
# 555 "env.fs"
let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _185_894 = (find_edge order (i, k))
in (let _185_893 = (find_edge order (j, k))
in (_185_894, _185_893)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _83_950, _83_952) -> begin
if ((let _185_895 = (find_edge order (k, ub))
in (FStar_Util.is_some _185_895)) && (not ((let _185_896 = (find_edge order (ub, k))
in (FStar_Util.is_some _185_896))))) then begin
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
in (
# 572 "env.fs"
let effects = (
# 572 "env.fs"
let _83_965 = env.effects
in {decls = _83_965.decls; order = order; joins = joins})
in (
# 575 "env.fs"
let _83_968 = env
in {solver = _83_968.solver; range = _83_968.range; curmodule = _83_968.curmodule; gamma = _83_968.gamma; gamma_cache = _83_968.gamma_cache; modules = _83_968.modules; expected_typ = _83_968.expected_typ; sigtab = _83_968.sigtab; is_pattern = _83_968.is_pattern; instantiate_imp = _83_968.instantiate_imp; effects = effects; generalize = _83_968.generalize; letrecs = _83_968.letrecs; top_level = _83_968.top_level; check_uvars = _83_968.check_uvars; use_eq = _83_968.use_eq; is_iface = _83_968.is_iface; admit = _83_968.admit; default_effects = _83_968.default_effects; type_of = _83_968.type_of; use_bv_sorts = _83_968.use_bv_sorts})))))))))))))
end
| _83_971 -> begin
env
end))

# 582 "env.fs"
let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (let _185_945 = (
# 582 "env.fs"
let _83_974 = env
in (let _185_944 = (let _185_943 = (let _185_942 = (let _185_941 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_185_941, s))
in Binding_sig (_185_942))
in (_185_943)::env.gamma)
in {solver = _83_974.solver; range = _83_974.range; curmodule = _83_974.curmodule; gamma = _185_944; gamma_cache = _83_974.gamma_cache; modules = _83_974.modules; expected_typ = _83_974.expected_typ; sigtab = _83_974.sigtab; is_pattern = _83_974.is_pattern; instantiate_imp = _83_974.instantiate_imp; effects = _83_974.effects; generalize = _83_974.generalize; letrecs = _83_974.letrecs; top_level = _83_974.top_level; check_uvars = _83_974.check_uvars; use_eq = _83_974.use_eq; is_iface = _83_974.is_iface; admit = _83_974.admit; default_effects = _83_974.default_effects; type_of = _83_974.type_of; use_bv_sorts = _83_974.use_bv_sorts}))
in (build_lattice _185_945 s)))

# 584 "env.fs"
let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (let _185_956 = (
# 584 "env.fs"
let _83_979 = env
in (let _185_955 = (let _185_954 = (let _185_953 = (let _185_952 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_185_952, s, us))
in Binding_sig_inst (_185_953))
in (_185_954)::env.gamma)
in {solver = _83_979.solver; range = _83_979.range; curmodule = _83_979.curmodule; gamma = _185_955; gamma_cache = _83_979.gamma_cache; modules = _83_979.modules; expected_typ = _83_979.expected_typ; sigtab = _83_979.sigtab; is_pattern = _83_979.is_pattern; instantiate_imp = _83_979.instantiate_imp; effects = _83_979.effects; generalize = _83_979.generalize; letrecs = _83_979.letrecs; top_level = _83_979.top_level; check_uvars = _83_979.check_uvars; use_eq = _83_979.use_eq; is_iface = _83_979.is_iface; admit = _83_979.admit; default_effects = _83_979.default_effects; type_of = _83_979.type_of; use_bv_sorts = _83_979.use_bv_sorts}))
in (build_lattice _185_956 s)))

# 586 "env.fs"
let push_local_binding : env  ->  binding  ->  env = (fun env b -> (
# 586 "env.fs"
let _83_983 = env
in {solver = _83_983.solver; range = _83_983.range; curmodule = _83_983.curmodule; gamma = (b)::env.gamma; gamma_cache = _83_983.gamma_cache; modules = _83_983.modules; expected_typ = _83_983.expected_typ; sigtab = _83_983.sigtab; is_pattern = _83_983.is_pattern; instantiate_imp = _83_983.instantiate_imp; effects = _83_983.effects; generalize = _83_983.generalize; letrecs = _83_983.letrecs; top_level = _83_983.top_level; check_uvars = _83_983.check_uvars; use_eq = _83_983.use_eq; is_iface = _83_983.is_iface; admit = _83_983.admit; default_effects = _83_983.default_effects; type_of = _83_983.type_of; use_bv_sorts = _83_983.use_bv_sorts}))

# 588 "env.fs"
let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))

# 590 "env.fs"
let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _83_993 -> (match (_83_993) with
| (x, _83_992) -> begin
(push_bv env x)
end)) env bs))

# 593 "env.fs"
let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(
# 595 "env.fs"
let _83_998 = ()
in (
# 596 "env.fs"
let x = (
# 596 "env.fs"
let _83_1000 = x
in {FStar_Syntax_Syntax.ppname = _83_1000.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _83_1000.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (lid) -> begin
Binding_lid ((lid, t))
end))

# 601 "env.fs"
let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))

# 603 "env.fs"
let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (
# 604 "env.fs"
let _83_1010 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (
# 605 "env.fs"
let _83_1012 = env
in {solver = _83_1012.solver; range = _83_1012.range; curmodule = _83_1012.curmodule; gamma = []; gamma_cache = _83_1012.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _83_1012.sigtab; is_pattern = _83_1012.is_pattern; instantiate_imp = _83_1012.instantiate_imp; effects = _83_1012.effects; generalize = _83_1012.generalize; letrecs = _83_1012.letrecs; top_level = _83_1012.top_level; check_uvars = _83_1012.check_uvars; use_eq = _83_1012.use_eq; is_iface = _83_1012.is_iface; admit = _83_1012.admit; default_effects = _83_1012.default_effects; type_of = _83_1012.type_of; use_bv_sorts = _83_1012.use_bv_sorts})))

# 610 "env.fs"
let push_univ_vars : env_t  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))

# 613 "env.fs"
let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (
# 614 "env.fs"
let _83_1020 = env
in {solver = _83_1020.solver; range = _83_1020.range; curmodule = _83_1020.curmodule; gamma = _83_1020.gamma; gamma_cache = _83_1020.gamma_cache; modules = _83_1020.modules; expected_typ = Some (t); sigtab = _83_1020.sigtab; is_pattern = _83_1020.is_pattern; instantiate_imp = _83_1020.instantiate_imp; effects = _83_1020.effects; generalize = _83_1020.generalize; letrecs = _83_1020.letrecs; top_level = _83_1020.top_level; check_uvars = _83_1020.check_uvars; use_eq = false; is_iface = _83_1020.is_iface; admit = _83_1020.admit; default_effects = _83_1020.default_effects; type_of = _83_1020.type_of; use_bv_sorts = _83_1020.use_bv_sorts}))

# 616 "env.fs"
let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

# 620 "env.fs"
let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> ((
# 621 "env.fs"
let _83_1027 = env
in {solver = _83_1027.solver; range = _83_1027.range; curmodule = _83_1027.curmodule; gamma = _83_1027.gamma; gamma_cache = _83_1027.gamma_cache; modules = _83_1027.modules; expected_typ = None; sigtab = _83_1027.sigtab; is_pattern = _83_1027.is_pattern; instantiate_imp = _83_1027.instantiate_imp; effects = _83_1027.effects; generalize = _83_1027.generalize; letrecs = _83_1027.letrecs; top_level = _83_1027.top_level; check_uvars = _83_1027.check_uvars; use_eq = false; is_iface = _83_1027.is_iface; admit = _83_1027.admit; default_effects = _83_1027.default_effects; type_of = _83_1027.type_of; use_bv_sorts = _83_1027.use_bv_sorts}), (expected_typ env)))

# 623 "env.fs"
let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (
# 624 "env.fs"
let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (
# 626 "env.fs"
let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
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
in (
# 632 "env.fs"
let _83_1041 = (add_sigelts env sigs)
in (
# 633 "env.fs"
let _83_1043 = (FStar_Util.smap_clear env.gamma_cache)
in (
# 634 "env.fs"
let _83_1045 = env
in {solver = _83_1045.solver; range = _83_1045.range; curmodule = empty_lid; gamma = []; gamma_cache = _83_1045.gamma_cache; modules = (m)::env.modules; expected_typ = _83_1045.expected_typ; sigtab = _83_1045.sigtab; is_pattern = _83_1045.is_pattern; instantiate_imp = _83_1045.instantiate_imp; effects = _83_1045.effects; generalize = _83_1045.generalize; letrecs = _83_1045.letrecs; top_level = _83_1045.top_level; check_uvars = _83_1045.check_uvars; use_eq = _83_1045.use_eq; is_iface = _83_1045.is_iface; admit = _83_1045.admit; default_effects = _83_1045.default_effects; type_of = _83_1045.type_of; use_bv_sorts = _83_1045.use_bv_sorts}))))))

# 642 "env.fs"
let uvars_in_env : env  ->  (((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) Prims.list * (((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  Prims.bool)) = (fun env -> (
# 643 "env.fs"
let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (
# 644 "env.fs"
let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (
# 645 "env.fs"
let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| Binding_univ (_83_1058)::tl -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _185_1021 = (let _185_1020 = (FStar_Syntax_Free.uvars t)
in (ext out _185_1020))
in (aux _185_1021 tl))
end
| (Binding_sig (_)::_) | (Binding_sig_inst (_)::_) -> begin
out
end))
in (aux no_uvs env.gamma)))))

# 654 "env.fs"
let univ_vars : env  ->  (FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar Prims.list * (FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  Prims.bool)) = (fun env -> (
# 655 "env.fs"
let no_univs = FStar_Syntax_Syntax.no_universe_uvars
in (
# 656 "env.fs"
let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (
# 657 "env.fs"
let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_sig_inst (_)::tl) | (Binding_univ (_)::tl) -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _185_1043 = (let _185_1042 = (FStar_Syntax_Free.univs t)
in (ext out _185_1042))
in (aux _185_1043 tl))
end
| Binding_sig (_83_1128)::_83_1126 -> begin
out
end))
in (aux no_univs env.gamma)))))

# 666 "env.fs"
let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _83_11 -> (match (_83_11) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))

# 674 "env.fs"
let binders_of_bindings : binding Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun bs -> (let _185_1050 = (let _185_1049 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _185_1049 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _185_1050 FStar_List.rev)))

# 676 "env.fs"
let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))

# 678 "env.fs"
let all_binders : env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (binders_of_bindings env.gamma))

# 680 "env.fs"
let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))

# 682 "env.fs"
let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (
# 683 "env.fs"
let keys = (FStar_List.fold_left (fun keys _83_12 -> (match (_83_12) with
| Binding_sig (lids, _83_1160) -> begin
(FStar_List.append lids keys)
end
| _83_1164 -> begin
keys
end)) [] env.gamma)
in (let _185_1074 = (sigtab env)
in (FStar_Util.smap_fold _185_1074 (fun _83_1166 v keys -> (let _185_1073 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _185_1073 keys))) keys))))

# 690 "env.fs"
let dummy_solver : solver_t = {init = (fun _83_1170 -> ()); push = (fun _83_1172 -> ()); pop = (fun _83_1174 -> ()); mark = (fun _83_1176 -> ()); reset_mark = (fun _83_1178 -> ()); commit_mark = (fun _83_1180 -> ()); encode_modul = (fun _83_1182 _83_1184 -> ()); encode_sig = (fun _83_1186 _83_1188 -> ()); solve = (fun _83_1190 _83_1192 -> ()); is_trivial = (fun _83_1194 _83_1196 -> false); finish = (fun _83_1198 -> ()); refresh = (fun _83_1199 -> ())}

# 705 "env.fs"
let no_solver_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t))  ->  env = (fun tc -> (let _185_1103 = (FStar_Ident.lid_of_path (("dummy")::[]) FStar_Range.dummyRange)
in (initial_env tc dummy_solver _185_1103)))




