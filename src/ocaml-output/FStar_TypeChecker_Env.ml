
open Prims
# 30 "FStar.TypeChecker.Env.fst"
type binding =
| Binding_var of FStar_Syntax_Syntax.bv
| Binding_lid of (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme)
| Binding_sig of (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
| Binding_univ of FStar_Syntax_Syntax.univ_name
| Binding_sig_inst of (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes)

# 31 "FStar.TypeChecker.Env.fst"
let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

# 32 "FStar.TypeChecker.Env.fst"
let is_Binding_lid = (fun _discr_ -> (match (_discr_) with
| Binding_lid (_) -> begin
true
end
| _ -> begin
false
end))

# 33 "FStar.TypeChecker.Env.fst"
let is_Binding_sig = (fun _discr_ -> (match (_discr_) with
| Binding_sig (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "FStar.TypeChecker.Env.fst"
let is_Binding_univ = (fun _discr_ -> (match (_discr_) with
| Binding_univ (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.TypeChecker.Env.fst"
let is_Binding_sig_inst = (fun _discr_ -> (match (_discr_) with
| Binding_sig_inst (_) -> begin
true
end
| _ -> begin
false
end))

# 31 "FStar.TypeChecker.Env.fst"
let ___Binding_var____0 : binding  ->  FStar_Syntax_Syntax.bv = (fun projectee -> (match (projectee) with
| Binding_var (_66_15) -> begin
_66_15
end))

# 32 "FStar.TypeChecker.Env.fst"
let ___Binding_lid____0 : binding  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme) = (fun projectee -> (match (projectee) with
| Binding_lid (_66_18) -> begin
_66_18
end))

# 33 "FStar.TypeChecker.Env.fst"
let ___Binding_sig____0 : binding  ->  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt) = (fun projectee -> (match (projectee) with
| Binding_sig (_66_21) -> begin
_66_21
end))

# 34 "FStar.TypeChecker.Env.fst"
let ___Binding_univ____0 : binding  ->  FStar_Syntax_Syntax.univ_name = (fun projectee -> (match (projectee) with
| Binding_univ (_66_24) -> begin
_66_24
end))

# 35 "FStar.TypeChecker.Env.fst"
let ___Binding_sig_inst____0 : binding  ->  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes) = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_66_27) -> begin
_66_27
end))

# 37 "FStar.TypeChecker.Env.fst"
type delta_level =
| NoDelta
| OnlyInline
| Unfold

# 38 "FStar.TypeChecker.Env.fst"
let is_NoDelta = (fun _discr_ -> (match (_discr_) with
| NoDelta (_) -> begin
true
end
| _ -> begin
false
end))

# 39 "FStar.TypeChecker.Env.fst"
let is_OnlyInline = (fun _discr_ -> (match (_discr_) with
| OnlyInline (_) -> begin
true
end
| _ -> begin
false
end))

# 40 "FStar.TypeChecker.Env.fst"
let is_Unfold = (fun _discr_ -> (match (_discr_) with
| Unfold (_) -> begin
true
end
| _ -> begin
false
end))

# 42 "FStar.TypeChecker.Env.fst"
type mlift =
FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ

# 44 "FStar.TypeChecker.Env.fst"
type edge =
{msource : FStar_Ident.lident; mtarget : FStar_Ident.lident; mlift : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ}

# 44 "FStar.TypeChecker.Env.fst"
let is_Mkedge : edge  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkedge"))))

# 49 "FStar.TypeChecker.Env.fst"
type effects =
{decls : FStar_Syntax_Syntax.eff_decl Prims.list; order : edge Prims.list; joins : (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list}

# 49 "FStar.TypeChecker.Env.fst"
let is_Mkeffects : effects  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeffects"))))

# 54 "FStar.TypeChecker.Env.fst"
type cached_elt =
((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either

# 55 "FStar.TypeChecker.Env.fst"
type env =
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ Prims.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap Prims.list; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; default_effects : (FStar_Ident.lident * FStar_Ident.lident) Prims.list; type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t); universe_of : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe; use_bv_sorts : Prims.bool} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit; solve : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit} 
 and guard_t =
{guard_f : FStar_TypeChecker_Common.guard_formula; deferred : FStar_TypeChecker_Common.deferred; univ_ineqs : FStar_TypeChecker_Common.univ_ineq Prims.list; implicits : (env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list}

# 55 "FStar.TypeChecker.Env.fst"
let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

# 79 "FStar.TypeChecker.Env.fst"
let is_Mksolver_t : solver_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksolver_t"))))

# 93 "FStar.TypeChecker.Env.fst"
let is_Mkguard_t : guard_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkguard_t"))))

# 99 "FStar.TypeChecker.Env.fst"
type env_t =
env

# 100 "FStar.TypeChecker.Env.fst"
type implicits =
(env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list

# 102 "FStar.TypeChecker.Env.fst"
type sigtable =
FStar_Syntax_Syntax.sigelt FStar_Util.smap

# 163 "FStar.TypeChecker.Env.fst"
let visible_at : delta_level  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun d q -> (match ((d, q)) with
| ((NoDelta, _)) | ((OnlyInline, FStar_Syntax_Syntax.Inline)) | ((Unfold, FStar_Syntax_Syntax.Inline)) | ((Unfold, FStar_Syntax_Syntax.Unfoldable)) -> begin
true
end
| _66_94 -> begin
false
end))

# 170 "FStar.TypeChecker.Env.fst"
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

# 178 "FStar.TypeChecker.Env.fst"
let default_table_size : Prims.int = 200

# 179 "FStar.TypeChecker.Env.fst"
let new_sigtab = (fun _66_116 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))

# 181 "FStar.TypeChecker.Env.fst"
let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t))  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun tc solver module_lid -> (let _145_376 = (FStar_Util.smap_create 100)
in (let _145_375 = (let _145_372 = (new_sigtab ())
in (_145_372)::[])
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _145_376; modules = []; expected_typ = None; sigtab = _145_375; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []; type_of = tc; universe_of = (fun g e -> FStar_Syntax_Syntax.U_zero); use_bv_sorts = false})))

# 207 "FStar.TypeChecker.Env.fst"
let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> (FStar_List.hd env.sigtab))

# 208 "FStar.TypeChecker.Env.fst"
let push : env  ->  Prims.string  ->  env = (fun env msg -> (
# 209 "FStar.TypeChecker.Env.fst"
let _66_125 = (env.solver.push msg)
in (
# 210 "FStar.TypeChecker.Env.fst"
let _66_127 = env
in (let _145_385 = (let _145_384 = (let _145_383 = (sigtab env)
in (FStar_Util.smap_copy _145_383))
in (_145_384)::env.sigtab)
in {solver = _66_127.solver; range = _66_127.range; curmodule = _66_127.curmodule; gamma = _66_127.gamma; gamma_cache = _66_127.gamma_cache; modules = _66_127.modules; expected_typ = _66_127.expected_typ; sigtab = _145_385; is_pattern = _66_127.is_pattern; instantiate_imp = _66_127.instantiate_imp; effects = _66_127.effects; generalize = _66_127.generalize; letrecs = _66_127.letrecs; top_level = _66_127.top_level; check_uvars = _66_127.check_uvars; use_eq = _66_127.use_eq; is_iface = _66_127.is_iface; admit = _66_127.admit; default_effects = _66_127.default_effects; type_of = _66_127.type_of; universe_of = _66_127.universe_of; use_bv_sorts = _66_127.use_bv_sorts}))))

# 211 "FStar.TypeChecker.Env.fst"
let mark : env  ->  env = (fun env -> (
# 212 "FStar.TypeChecker.Env.fst"
let _66_130 = (env.solver.mark "USER MARK")
in (
# 213 "FStar.TypeChecker.Env.fst"
let _66_132 = env
in (let _145_390 = (let _145_389 = (let _145_388 = (sigtab env)
in (FStar_Util.smap_copy _145_388))
in (_145_389)::env.sigtab)
in {solver = _66_132.solver; range = _66_132.range; curmodule = _66_132.curmodule; gamma = _66_132.gamma; gamma_cache = _66_132.gamma_cache; modules = _66_132.modules; expected_typ = _66_132.expected_typ; sigtab = _145_390; is_pattern = _66_132.is_pattern; instantiate_imp = _66_132.instantiate_imp; effects = _66_132.effects; generalize = _66_132.generalize; letrecs = _66_132.letrecs; top_level = _66_132.top_level; check_uvars = _66_132.check_uvars; use_eq = _66_132.use_eq; is_iface = _66_132.is_iface; admit = _66_132.admit; default_effects = _66_132.default_effects; type_of = _66_132.type_of; universe_of = _66_132.universe_of; use_bv_sorts = _66_132.use_bv_sorts}))))

# 214 "FStar.TypeChecker.Env.fst"
let commit_mark : env  ->  env = (fun env -> (
# 215 "FStar.TypeChecker.Env.fst"
let _66_135 = (env.solver.commit_mark "USER MARK")
in (
# 216 "FStar.TypeChecker.Env.fst"
let sigtab = (match (env.sigtab) with
| hd::_66_139::tl -> begin
(hd)::tl
end
| _66_144 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 219 "FStar.TypeChecker.Env.fst"
let _66_146 = env
in {solver = _66_146.solver; range = _66_146.range; curmodule = _66_146.curmodule; gamma = _66_146.gamma; gamma_cache = _66_146.gamma_cache; modules = _66_146.modules; expected_typ = _66_146.expected_typ; sigtab = sigtab; is_pattern = _66_146.is_pattern; instantiate_imp = _66_146.instantiate_imp; effects = _66_146.effects; generalize = _66_146.generalize; letrecs = _66_146.letrecs; top_level = _66_146.top_level; check_uvars = _66_146.check_uvars; use_eq = _66_146.use_eq; is_iface = _66_146.is_iface; admit = _66_146.admit; default_effects = _66_146.default_effects; type_of = _66_146.type_of; universe_of = _66_146.universe_of; use_bv_sorts = _66_146.use_bv_sorts}))))

# 220 "FStar.TypeChecker.Env.fst"
let reset_mark : env  ->  env = (fun env -> (
# 221 "FStar.TypeChecker.Env.fst"
let _66_149 = (env.solver.reset_mark "USER MARK")
in (
# 222 "FStar.TypeChecker.Env.fst"
let _66_151 = env
in (let _145_395 = (FStar_List.tl env.sigtab)
in {solver = _66_151.solver; range = _66_151.range; curmodule = _66_151.curmodule; gamma = _66_151.gamma; gamma_cache = _66_151.gamma_cache; modules = _66_151.modules; expected_typ = _66_151.expected_typ; sigtab = _145_395; is_pattern = _66_151.is_pattern; instantiate_imp = _66_151.instantiate_imp; effects = _66_151.effects; generalize = _66_151.generalize; letrecs = _66_151.letrecs; top_level = _66_151.top_level; check_uvars = _66_151.check_uvars; use_eq = _66_151.use_eq; is_iface = _66_151.is_iface; admit = _66_151.admit; default_effects = _66_151.default_effects; type_of = _66_151.type_of; universe_of = _66_151.universe_of; use_bv_sorts = _66_151.use_bv_sorts}))))

# 223 "FStar.TypeChecker.Env.fst"
let pop : env  ->  Prims.string  ->  env = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(FStar_All.failwith "Too many pops")
end
| _66_161::tl -> begin
(
# 227 "FStar.TypeChecker.Env.fst"
let _66_163 = (env.solver.pop msg)
in (
# 228 "FStar.TypeChecker.Env.fst"
let _66_165 = env
in {solver = _66_165.solver; range = _66_165.range; curmodule = _66_165.curmodule; gamma = _66_165.gamma; gamma_cache = _66_165.gamma_cache; modules = _66_165.modules; expected_typ = _66_165.expected_typ; sigtab = tl; is_pattern = _66_165.is_pattern; instantiate_imp = _66_165.instantiate_imp; effects = _66_165.effects; generalize = _66_165.generalize; letrecs = _66_165.letrecs; top_level = _66_165.top_level; check_uvars = _66_165.check_uvars; use_eq = _66_165.use_eq; is_iface = _66_165.is_iface; admit = _66_165.admit; default_effects = _66_165.default_effects; type_of = _66_165.type_of; universe_of = _66_165.universe_of; use_bv_sorts = _66_165.use_bv_sorts}))
end))

# 233 "FStar.TypeChecker.Env.fst"
let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> ((let _145_405 = (FStar_ST.read FStar_Options.debug)
in (FStar_All.pipe_right _145_405 (FStar_Util.for_some (fun x -> ((env.curmodule.FStar_Ident.str = "") || (env.curmodule.FStar_Ident.str = x)))))) && (FStar_Options.debug_level_geq l)))

# 236 "FStar.TypeChecker.Env.fst"
let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(
# 236 "FStar.TypeChecker.Env.fst"
let _66_172 = e
in {solver = _66_172.solver; range = r; curmodule = _66_172.curmodule; gamma = _66_172.gamma; gamma_cache = _66_172.gamma_cache; modules = _66_172.modules; expected_typ = _66_172.expected_typ; sigtab = _66_172.sigtab; is_pattern = _66_172.is_pattern; instantiate_imp = _66_172.instantiate_imp; effects = _66_172.effects; generalize = _66_172.generalize; letrecs = _66_172.letrecs; top_level = _66_172.top_level; check_uvars = _66_172.check_uvars; use_eq = _66_172.use_eq; is_iface = _66_172.is_iface; admit = _66_172.admit; default_effects = _66_172.default_effects; type_of = _66_172.type_of; universe_of = _66_172.universe_of; use_bv_sorts = _66_172.use_bv_sorts})
end)

# 237 "FStar.TypeChecker.Env.fst"
let get_range : env  ->  FStar_Range.range = (fun e -> e.range)

# 242 "FStar.TypeChecker.Env.fst"
let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)

# 243 "FStar.TypeChecker.Env.fst"
let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)

# 244 "FStar.TypeChecker.Env.fst"
let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (
# 244 "FStar.TypeChecker.Env.fst"
let _66_179 = env
in {solver = _66_179.solver; range = _66_179.range; curmodule = lid; gamma = _66_179.gamma; gamma_cache = _66_179.gamma_cache; modules = _66_179.modules; expected_typ = _66_179.expected_typ; sigtab = _66_179.sigtab; is_pattern = _66_179.is_pattern; instantiate_imp = _66_179.instantiate_imp; effects = _66_179.effects; generalize = _66_179.generalize; letrecs = _66_179.letrecs; top_level = _66_179.top_level; check_uvars = _66_179.check_uvars; use_eq = _66_179.use_eq; is_iface = _66_179.is_iface; admit = _66_179.admit; default_effects = _66_179.default_effects; type_of = _66_179.type_of; universe_of = _66_179.universe_of; use_bv_sorts = _66_179.use_bv_sorts}))

# 245 "FStar.TypeChecker.Env.fst"
let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))

# 246 "FStar.TypeChecker.Env.fst"
let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (let _145_429 = (sigtab env)
in (FStar_Util.smap_try_find _145_429 (FStar_Ident.text_of_lid lid))))

# 248 "FStar.TypeChecker.Env.fst"
let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))

# 251 "FStar.TypeChecker.Env.fst"
let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _145_434 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _145_434)))

# 255 "FStar.TypeChecker.Env.fst"
let new_u_univ = (fun _66_188 -> (let _145_436 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_145_436)))

# 258 "FStar.TypeChecker.Env.fst"
let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match ((ts, us)) with
| (([], t), []) -> begin
([], t)
end
| ((formals, t), _66_201) -> begin
(
# 262 "FStar.TypeChecker.Env.fst"
let _66_203 = ()
in (
# 263 "FStar.TypeChecker.Env.fst"
let n = ((FStar_List.length formals) - 1)
in (
# 264 "FStar.TypeChecker.Env.fst"
let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN (((n - i), u)))))
in (let _145_443 = (FStar_Syntax_Subst.subst vs t)
in (us, _145_443)))))
end))

# 268 "FStar.TypeChecker.Env.fst"
let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _66_1 -> (match (_66_1) with
| ([], t) -> begin
([], t)
end
| (us, t) -> begin
(
# 271 "FStar.TypeChecker.Env.fst"
let us' = (FStar_All.pipe_right us (FStar_List.map (fun _66_216 -> (new_u_univ ()))))
in (inst_tscheme_with (us, t) us'))
end))

# 274 "FStar.TypeChecker.Env.fst"
let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed _66_224 -> (match (_66_224) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(
# 277 "FStar.TypeChecker.Env.fst"
let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in (
# 278 "FStar.TypeChecker.Env.fst"
let _66_227 = if ((FStar_List.length insts) <> (FStar_List.length univs)) then begin
(let _145_459 = (let _145_458 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _145_457 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _145_456 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _145_455 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _145_458 _145_457 _145_456 _145_455)))))
in (FStar_All.failwith _145_459))
end else begin
()
end
in (let _145_460 = (inst_tscheme_with ((FStar_List.append ed.FStar_Syntax_Syntax.univs us), t) insts)
in (Prims.snd _145_460))))
end
| _66_230 -> begin
(let _145_462 = (let _145_461 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _145_461))
in (FStar_All.failwith _145_462))
end)
end))

# 285 "FStar.TypeChecker.Env.fst"
type tri =
| Yes
| No
| Maybe

# 286 "FStar.TypeChecker.Env.fst"
let is_Yes = (fun _discr_ -> (match (_discr_) with
| Yes (_) -> begin
true
end
| _ -> begin
false
end))

# 287 "FStar.TypeChecker.Env.fst"
let is_No = (fun _discr_ -> (match (_discr_) with
| No (_) -> begin
true
end
| _ -> begin
false
end))

# 288 "FStar.TypeChecker.Env.fst"
let is_Maybe = (fun _discr_ -> (match (_discr_) with
| Maybe (_) -> begin
true
end
| _ -> begin
false
end))

# 290 "FStar.TypeChecker.Env.fst"
let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (
# 291 "FStar.TypeChecker.Env.fst"
let cur = (current_module env)
in if (l.FStar_Ident.nsstr = cur.FStar_Ident.str) then begin
Yes
end else begin
if (FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str) then begin
(
# 294 "FStar.TypeChecker.Env.fst"
let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (
# 295 "FStar.TypeChecker.Env.fst"
let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (
# 296 "FStar.TypeChecker.Env.fst"
let rec aux = (fun c l -> (match ((c, l)) with
| ([], _66_241) -> begin
Maybe
end
| (_66_244, []) -> begin
No
end
| (hd::tl, hd'::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _66_255 -> begin
No
end))
in (aux cur lns))))
end else begin
No
end
end))

# 304 "FStar.TypeChecker.Env.fst"
let lookup_qname : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either Prims.option = (fun env lid -> (
# 305 "FStar.TypeChecker.Env.fst"
let cur_mod = (in_cur_mod env lid)
in (
# 306 "FStar.TypeChecker.Env.fst"
let cache = (fun t -> (
# 306 "FStar.TypeChecker.Env.fst"
let _66_261 = (FStar_Util.smap_add env.gamma_cache lid.FStar_Ident.str t)
in Some (t)))
in (
# 307 "FStar.TypeChecker.Env.fst"
let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find env.gamma_cache lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _66_2 -> (match (_66_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _145_482 = (let _145_481 = (inst_tscheme t)
in FStar_Util.Inl (_145_481))
in Some (_145_482))
end else begin
None
end
end
| Binding_sig (_66_270, FStar_Syntax_Syntax.Sig_bundle (ses, _66_273, _66_275, _66_277)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _145_484 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _145_484 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr ((se, None))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(
# 318 "FStar.TypeChecker.Env.fst"
let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_66_290) -> begin
Some (t)
end
| _66_293 -> begin
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
| _66_300 -> begin
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

# 335 "FStar.TypeChecker.Env.fst"
let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| None -> begin
false
end
| Some (_66_310) -> begin
true
end))

# 339 "FStar.TypeChecker.Env.fst"
let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _66_316, _66_318, _66_320) -> begin
(add_sigelts env ses)
end
| _66_324 -> begin
(
# 342 "FStar.TypeChecker.Env.fst"
let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _145_498 = (sigtab env)
in (FStar_Util.smap_add _145_498 l.FStar_Ident.str se))) lids))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))

# 351 "FStar.TypeChecker.Env.fst"
let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun _66_3 -> (match (_66_3) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _66_335 -> begin
None
end))))

# 357 "FStar.TypeChecker.Env.fst"
let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _66_4 -> (match (_66_4) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _66_342 -> begin
false
end)) env.gamma) FStar_Option.isSome))

# 363 "FStar.TypeChecker.Env.fst"
let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_66_346, lb::[]), _66_351, _66_353, _66_355) -> begin
(let _145_518 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_145_518))
end
| FStar_Syntax_Syntax.Sig_let ((_66_359, lbs), _66_363, _66_365, _66_367) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_66_372) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (lid') -> begin
if (FStar_Ident.lid_equals lid lid') then begin
(let _145_520 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_145_520))
end else begin
None
end
end)))
end
| _66_377 -> begin
None
end))

# 377 "FStar.TypeChecker.Env.fst"
let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _145_528 = (let _145_527 = (let _145_526 = (variable_not_found bv)
in (let _145_525 = (FStar_Syntax_Syntax.range_of_bv bv)
in (_145_526, _145_525)))
in FStar_Syntax_Syntax.Error (_145_527))
in (Prims.raise _145_528))
end
| Some (t) -> begin
t
end))

# 382 "FStar.TypeChecker.Env.fst"
let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _66_386) -> begin
(let _145_534 = (let _145_533 = (let _145_532 = (let _145_531 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _145_531))
in (ne.FStar_Syntax_Syntax.univs, _145_532))
in (inst_tscheme _145_533))
in Some (_145_534))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _66_393, _66_395, _66_397) -> begin
(let _145_538 = (let _145_537 = (let _145_536 = (let _145_535 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _145_535))
in (us, _145_536))
in (inst_tscheme _145_537))
in Some (_145_538))
end
| _66_401 -> begin
None
end))

# 392 "FStar.TypeChecker.Env.fst"
let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_66_411, t) -> begin
Some (t)
end)
end
| _66_416 -> begin
None
end))

# 401 "FStar.TypeChecker.Env.fst"
let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env lid -> (
# 402 "FStar.TypeChecker.Env.fst"
let mapper = (fun _66_5 -> (match (_66_5) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_66_423, uvs, t, _66_427, _66_429, _66_431, _66_433, _66_435), None) -> begin
(let _145_549 = (inst_tscheme (uvs, t))
in Some (_145_549))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _66_446), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _145_550 = (inst_tscheme (uvs, t))
in Some (_145_550))
end else begin
None
end
end else begin
(let _145_551 = (inst_tscheme (uvs, t))
in Some (_145_551))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _66_457, _66_459, _66_461, _66_463), None) -> begin
(match (tps) with
| [] -> begin
(let _145_553 = (inst_tscheme (uvs, k))
in (FStar_All.pipe_left (fun _145_552 -> Some (_145_552)) _145_553))
end
| _66_471 -> begin
(let _145_558 = (let _145_557 = (let _145_556 = (let _145_555 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _145_555))
in (uvs, _145_556))
in (inst_tscheme _145_557))
in (FStar_All.pipe_left (fun _145_554 -> Some (_145_554)) _145_558))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _66_477, _66_479, _66_481, _66_483), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _145_560 = (inst_tscheme_with (uvs, k) us)
in (FStar_All.pipe_left (fun _145_559 -> Some (_145_559)) _145_560))
end
| _66_492 -> begin
(let _145_565 = (let _145_564 = (let _145_563 = (let _145_562 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _145_562))
in (uvs, _145_563))
in (inst_tscheme_with _145_564 us))
in (FStar_All.pipe_left (fun _145_561 -> Some (_145_561)) _145_565))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_66_496), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _66_501 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _145_566 = (lookup_qname env lid)
in (FStar_Util.bind_opt _145_566 mapper))) with
| Some (us, t) -> begin
Some ((us, (
# 436 "FStar.TypeChecker.Env.fst"
let _66_507 = t
in {FStar_Syntax_Syntax.n = _66_507.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _66_507.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _66_507.FStar_Syntax_Syntax.vars})))
end
| None -> begin
None
end)))

# 439 "FStar.TypeChecker.Env.fst"
let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _145_573 = (let _145_572 = (let _145_571 = (name_not_found l)
in (_145_571, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_145_572))
in (Prims.raise _145_573))
end
| Some (x) -> begin
x
end))

# 444 "FStar.TypeChecker.Env.fst"
let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_66_518, uvs, t, _66_522, _66_524), None)) -> begin
(inst_tscheme (uvs, t))
end
| _66_532 -> begin
(let _145_580 = (let _145_579 = (let _145_578 = (name_not_found lid)
in (_145_578, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_145_579))
in (Prims.raise _145_580))
end))

# 449 "FStar.TypeChecker.Env.fst"
let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_66_536, uvs, t, _66_540, _66_542, _66_544, _66_546, _66_548), None)) -> begin
(inst_tscheme (uvs, t))
end
| _66_556 -> begin
(let _145_587 = (let _145_586 = (let _145_585 = (name_not_found lid)
in (_145_585, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_145_586))
in (Prims.raise _145_587))
end))

# 454 "FStar.TypeChecker.Env.fst"
let lookup_definition : delta_level  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_66_566, lbs), _66_570, _66_572, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (
# 460 "FStar.TypeChecker.Env.fst"
let lid' = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Ident.lid_equals lid lid') then begin
(let _145_596 = (let _145_595 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (lb.FStar_Syntax_Syntax.lbunivs, _145_595))
in Some (_145_596))
end else begin
None
end)))
end
| _66_579 -> begin
None
end)
end
| _66_581 -> begin
None
end))

# 468 "FStar.TypeChecker.Env.fst"
let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _145_603 = (let _145_602 = (let _145_601 = (name_not_found ftv)
in (_145_601, (FStar_Ident.range_of_lid ftv)))
in FStar_Syntax_Syntax.Error (_145_602))
in (Prims.raise _145_603))
end
| Some (k) -> begin
k
end))

# 473 "FStar.TypeChecker.Env.fst"
let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (
# 474 "FStar.TypeChecker.Env.fst"
let fail = (fun _66_591 -> (match (()) with
| () -> begin
(let _145_614 = (let _145_613 = (FStar_Util.string_of_int i)
in (let _145_612 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _145_613 _145_612)))
in (FStar_All.failwith _145_614))
end))
in (
# 475 "FStar.TypeChecker.Env.fst"
let _66_595 = (lookup_datacon env lid)
in (match (_66_595) with
| (_66_593, t) -> begin
(match ((let _145_615 = (FStar_Syntax_Subst.compress t)
in _145_615.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _66_598) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(
# 480 "FStar.TypeChecker.Env.fst"
let b = (FStar_List.nth binders i)
in (let _145_616 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _145_616 Prims.fst)))
end
end
| _66_603 -> begin
(fail ())
end)
end))))

# 484 "FStar.TypeChecker.Env.fst"
let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_66_607, uvs, t, q, _66_612), None)) -> begin
Some (((uvs, t), q))
end
| _66_620 -> begin
None
end))

# 489 "FStar.TypeChecker.Env.fst"
let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _66_630), None)) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _66_6 -> (match (_66_6) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _66_640 -> begin
false
end)))) then begin
None
end else begin
(
# 494 "FStar.TypeChecker.Env.fst"
let insts = if (FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid) then begin
(univ)::(FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]
end else begin
(univ)::[]
end
in (match ((binders, univs)) with
| ([], _66_644) -> begin
(FStar_All.failwith "Unexpected effect abbreviation with no arguments")
end
| (_66_647, _66_654::_66_651::_66_649) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(let _145_630 = (let _145_629 = (FStar_Syntax_Print.lid_to_string lid)
in (let _145_628 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _145_629 _145_628)))
in (FStar_All.failwith _145_630))
end
| _66_658 -> begin
(
# 502 "FStar.TypeChecker.Env.fst"
let _66_662 = (let _145_632 = (let _145_631 = (FStar_Syntax_Util.arrow binders c)
in (univs, _145_631))
in (inst_tscheme_with _145_632 insts))
in (match (_66_662) with
| (_66_660, t) -> begin
(match ((let _145_633 = (FStar_Syntax_Subst.compress t)
in _145_633.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some ((binders, c))
end
| _66_668 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end))
end
end
| _66_670 -> begin
None
end))

# 511 "FStar.TypeChecker.Env.fst"
let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_66_674, _66_676, _66_678, _66_680, _66_682, dcs, _66_685, _66_687), _66_691)) -> begin
dcs
end
| _66_696 -> begin
[]
end))

# 516 "FStar.TypeChecker.Env.fst"
let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_66_700, _66_702, _66_704, l, _66_707, _66_709, _66_711, _66_713), _66_717)) -> begin
l
end
| _66_722 -> begin
(let _145_643 = (let _145_642 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _145_642))
in (FStar_All.failwith _145_643))
end))

# 521 "FStar.TypeChecker.Env.fst"
let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_66_726, _66_728, _66_730, _66_732, _66_734, _66_736, _66_738, _66_740), _66_744)) -> begin
true
end
| _66_749 -> begin
false
end))

# 526 "FStar.TypeChecker.Env.fst"
let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_66_753, _66_755, _66_757, _66_759, _66_761, _66_763, tags, _66_766), _66_770)) -> begin
(FStar_Util.for_some (fun _66_7 -> (match (_66_7) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _66_782 -> begin
false
end)) tags)
end
| _66_784 -> begin
false
end))

# 532 "FStar.TypeChecker.Env.fst"
let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_66_788, _66_790, _66_792, quals, _66_795), _66_799)) -> begin
(FStar_Util.for_some (fun _66_8 -> (match (_66_8) with
| FStar_Syntax_Syntax.Projector (_66_805) -> begin
true
end
| _66_808 -> begin
false
end)) quals)
end
| _66_810 -> begin
false
end))

# 541 "FStar.TypeChecker.Env.fst"
let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))

# 544 "FStar.TypeChecker.Env.fst"
let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _145_669 = (let _145_668 = (let _145_667 = (name_not_found l)
in (_145_667, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_145_668))
in (Prims.raise _145_669))
end
| Some (md) -> begin
md
end))

# 549 "FStar.TypeChecker.Env.fst"
let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
(l1, (fun t wp -> wp), (fun t wp -> wp))
end else begin
if (((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid))) then begin
(FStar_Syntax_Const.effect_GTot_lid, (fun t wp -> wp), (fun t wp -> wp))
end else begin
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _66_838 -> (match (_66_838) with
| (m1, m2, _66_833, _66_835, _66_837) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _145_745 = (let _145_744 = (let _145_743 = (let _145_742 = (FStar_Syntax_Print.lid_to_string l1)
in (let _145_741 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _145_742 _145_741)))
in (_145_743, env.range))
in FStar_Syntax_Syntax.Error (_145_744))
in (Prims.raise _145_745))
end
| Some (_66_841, _66_843, m3, j1, j2) -> begin
(m3, j1, j2)
end)
end
end)

# 559 "FStar.TypeChecker.Env.fst"
let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge Prims.option = (fun env l1 l2 -> if ((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid))) then begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end else begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end)

# 565 "FStar.TypeChecker.Env.fst"
let wp_sig_aux : FStar_Syntax_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun decls m -> (match ((FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))))) with
| None -> begin
(let _145_760 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _145_760))
end
| Some (md) -> begin
(
# 569 "FStar.TypeChecker.Env.fst"
let _66_864 = (inst_tscheme (md.FStar_Syntax_Syntax.univs, md.FStar_Syntax_Syntax.signature))
in (match (_66_864) with
| (_66_862, s) -> begin
(
# 570 "FStar.TypeChecker.Env.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match ((md.FStar_Syntax_Syntax.binders, s.FStar_Syntax_Syntax.n)) with
| ([], FStar_Syntax_Syntax.Tm_arrow ((a, _66_877)::(wp, _66_873)::(wlp, _66_869)::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _66_885 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))

# 575 "FStar.TypeChecker.Env.fst"
let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))

# 577 "FStar.TypeChecker.Env.fst"
let default_effect : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (FStar_Util.find_map env.default_effects (fun _66_892 -> (match (_66_892) with
| (l', m) -> begin
if (FStar_Ident.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))

# 579 "FStar.TypeChecker.Env.fst"
let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, _66_897, _66_899, c, quals, r) -> begin
(match ((FStar_Util.find_map quals (fun _66_9 -> (match (_66_9) with
| FStar_Syntax_Syntax.DefaultEffect (n) -> begin
n
end
| _66_909 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(
# 583 "FStar.TypeChecker.Env.fst"
let _66_913 = env
in {solver = _66_913.solver; range = _66_913.range; curmodule = _66_913.curmodule; gamma = _66_913.gamma; gamma_cache = _66_913.gamma_cache; modules = _66_913.modules; expected_typ = _66_913.expected_typ; sigtab = _66_913.sigtab; is_pattern = _66_913.is_pattern; instantiate_imp = _66_913.instantiate_imp; effects = _66_913.effects; generalize = _66_913.generalize; letrecs = _66_913.letrecs; top_level = _66_913.top_level; check_uvars = _66_913.check_uvars; use_eq = _66_913.use_eq; is_iface = _66_913.is_iface; admit = _66_913.admit; default_effects = ((e, l))::env.default_effects; type_of = _66_913.type_of; universe_of = _66_913.universe_of; use_bv_sorts = _66_913.use_bv_sorts})
end)
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _66_917) -> begin
(
# 586 "FStar.TypeChecker.Env.fst"
let effects = (
# 586 "FStar.TypeChecker.Env.fst"
let _66_920 = env.effects
in {decls = (ne)::env.effects.decls; order = _66_920.order; joins = _66_920.joins})
in (
# 587 "FStar.TypeChecker.Env.fst"
let _66_923 = env
in {solver = _66_923.solver; range = _66_923.range; curmodule = _66_923.curmodule; gamma = _66_923.gamma; gamma_cache = _66_923.gamma_cache; modules = _66_923.modules; expected_typ = _66_923.expected_typ; sigtab = _66_923.sigtab; is_pattern = _66_923.is_pattern; instantiate_imp = _66_923.instantiate_imp; effects = effects; generalize = _66_923.generalize; letrecs = _66_923.letrecs; top_level = _66_923.top_level; check_uvars = _66_923.check_uvars; use_eq = _66_923.use_eq; is_iface = _66_923.is_iface; admit = _66_923.admit; default_effects = _66_923.default_effects; type_of = _66_923.type_of; universe_of = _66_923.universe_of; use_bv_sorts = _66_923.use_bv_sorts}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _66_927) -> begin
(
# 590 "FStar.TypeChecker.Env.fst"
let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _145_781 = (e1.mlift r wp1)
in (e2.mlift r _145_781)))})
in (
# 595 "FStar.TypeChecker.Env.fst"
let mk_lift = (fun lift_t r wp1 -> (
# 596 "FStar.TypeChecker.Env.fst"
let _66_942 = (inst_tscheme lift_t)
in (match (_66_942) with
| (_66_940, lift_t) -> begin
(let _145_793 = (let _145_792 = (let _145_791 = (let _145_790 = (FStar_Syntax_Syntax.as_arg r)
in (let _145_789 = (let _145_788 = (FStar_Syntax_Syntax.as_arg wp1)
in (_145_788)::[])
in (_145_790)::_145_789))
in (lift_t, _145_791))
in FStar_Syntax_Syntax.Tm_app (_145_792))
in (FStar_Syntax_Syntax.mk _145_793 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (
# 599 "FStar.TypeChecker.Env.fst"
let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub.FStar_Syntax_Syntax.lift)}
in (
# 603 "FStar.TypeChecker.Env.fst"
let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (
# 608 "FStar.TypeChecker.Env.fst"
let print_mlift = (fun l -> (
# 609 "FStar.TypeChecker.Env.fst"
let arg = (let _145_810 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _145_810 None))
in (
# 610 "FStar.TypeChecker.Env.fst"
let wp = (let _145_811 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _145_811 None))
in (let _145_812 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _145_812)))))
in (
# 612 "FStar.TypeChecker.Env.fst"
let order = (edge)::env.effects.order
in (
# 614 "FStar.TypeChecker.Env.fst"
let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (
# 616 "FStar.TypeChecker.Env.fst"
let find_edge = (fun order _66_959 -> (match (_66_959) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _145_818 -> Some (_145_818)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (
# 625 "FStar.TypeChecker.Env.fst"
let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _145_826 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _145_825 = (find_edge order (i, k))
in (let _145_824 = (find_edge order (k, j))
in (_145_825, _145_824)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _66_971 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _145_826))) order))
in (
# 636 "FStar.TypeChecker.Env.fst"
let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (
# 638 "FStar.TypeChecker.Env.fst"
let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (
# 641 "FStar.TypeChecker.Env.fst"
let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _145_918 = (find_edge order (i, k))
in (let _145_917 = (find_edge order (j, k))
in (_145_918, _145_917)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _66_988, _66_990) -> begin
if ((let _145_919 = (find_edge order (k, ub))
in (FStar_Util.is_some _145_919)) && (not ((let _145_920 = (find_edge order (ub, k))
in (FStar_Util.is_some _145_920))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _66_994 -> begin
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
# 658 "FStar.TypeChecker.Env.fst"
let effects = (
# 658 "FStar.TypeChecker.Env.fst"
let _66_1003 = env.effects
in {decls = _66_1003.decls; order = order; joins = joins})
in (
# 661 "FStar.TypeChecker.Env.fst"
let _66_1006 = env
in {solver = _66_1006.solver; range = _66_1006.range; curmodule = _66_1006.curmodule; gamma = _66_1006.gamma; gamma_cache = _66_1006.gamma_cache; modules = _66_1006.modules; expected_typ = _66_1006.expected_typ; sigtab = _66_1006.sigtab; is_pattern = _66_1006.is_pattern; instantiate_imp = _66_1006.instantiate_imp; effects = effects; generalize = _66_1006.generalize; letrecs = _66_1006.letrecs; top_level = _66_1006.top_level; check_uvars = _66_1006.check_uvars; use_eq = _66_1006.use_eq; is_iface = _66_1006.is_iface; admit = _66_1006.admit; default_effects = _66_1006.default_effects; type_of = _66_1006.type_of; universe_of = _66_1006.universe_of; use_bv_sorts = _66_1006.use_bv_sorts})))))))))))))
end
| _66_1009 -> begin
env
end))

# 668 "FStar.TypeChecker.Env.fst"
let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (let _145_969 = (
# 668 "FStar.TypeChecker.Env.fst"
let _66_1012 = env
in (let _145_968 = (let _145_967 = (let _145_966 = (let _145_965 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_145_965, s))
in Binding_sig (_145_966))
in (_145_967)::env.gamma)
in {solver = _66_1012.solver; range = _66_1012.range; curmodule = _66_1012.curmodule; gamma = _145_968; gamma_cache = _66_1012.gamma_cache; modules = _66_1012.modules; expected_typ = _66_1012.expected_typ; sigtab = _66_1012.sigtab; is_pattern = _66_1012.is_pattern; instantiate_imp = _66_1012.instantiate_imp; effects = _66_1012.effects; generalize = _66_1012.generalize; letrecs = _66_1012.letrecs; top_level = _66_1012.top_level; check_uvars = _66_1012.check_uvars; use_eq = _66_1012.use_eq; is_iface = _66_1012.is_iface; admit = _66_1012.admit; default_effects = _66_1012.default_effects; type_of = _66_1012.type_of; universe_of = _66_1012.universe_of; use_bv_sorts = _66_1012.use_bv_sorts}))
in (build_lattice _145_969 s)))

# 670 "FStar.TypeChecker.Env.fst"
let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (let _145_980 = (
# 670 "FStar.TypeChecker.Env.fst"
let _66_1017 = env
in (let _145_979 = (let _145_978 = (let _145_977 = (let _145_976 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_145_976, s, us))
in Binding_sig_inst (_145_977))
in (_145_978)::env.gamma)
in {solver = _66_1017.solver; range = _66_1017.range; curmodule = _66_1017.curmodule; gamma = _145_979; gamma_cache = _66_1017.gamma_cache; modules = _66_1017.modules; expected_typ = _66_1017.expected_typ; sigtab = _66_1017.sigtab; is_pattern = _66_1017.is_pattern; instantiate_imp = _66_1017.instantiate_imp; effects = _66_1017.effects; generalize = _66_1017.generalize; letrecs = _66_1017.letrecs; top_level = _66_1017.top_level; check_uvars = _66_1017.check_uvars; use_eq = _66_1017.use_eq; is_iface = _66_1017.is_iface; admit = _66_1017.admit; default_effects = _66_1017.default_effects; type_of = _66_1017.type_of; universe_of = _66_1017.universe_of; use_bv_sorts = _66_1017.use_bv_sorts}))
in (build_lattice _145_980 s)))

# 672 "FStar.TypeChecker.Env.fst"
let push_local_binding : env  ->  binding  ->  env = (fun env b -> (
# 672 "FStar.TypeChecker.Env.fst"
let _66_1021 = env
in {solver = _66_1021.solver; range = _66_1021.range; curmodule = _66_1021.curmodule; gamma = (b)::env.gamma; gamma_cache = _66_1021.gamma_cache; modules = _66_1021.modules; expected_typ = _66_1021.expected_typ; sigtab = _66_1021.sigtab; is_pattern = _66_1021.is_pattern; instantiate_imp = _66_1021.instantiate_imp; effects = _66_1021.effects; generalize = _66_1021.generalize; letrecs = _66_1021.letrecs; top_level = _66_1021.top_level; check_uvars = _66_1021.check_uvars; use_eq = _66_1021.use_eq; is_iface = _66_1021.is_iface; admit = _66_1021.admit; default_effects = _66_1021.default_effects; type_of = _66_1021.type_of; universe_of = _66_1021.universe_of; use_bv_sorts = _66_1021.use_bv_sorts}))

# 674 "FStar.TypeChecker.Env.fst"
let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))

# 676 "FStar.TypeChecker.Env.fst"
let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _66_1031 -> (match (_66_1031) with
| (x, _66_1030) -> begin
(push_bv env x)
end)) env bs))

# 679 "FStar.TypeChecker.Env.fst"
let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(
# 681 "FStar.TypeChecker.Env.fst"
let _66_1036 = ()
in (
# 682 "FStar.TypeChecker.Env.fst"
let x = (
# 682 "FStar.TypeChecker.Env.fst"
let _66_1038 = x
in {FStar_Syntax_Syntax.ppname = _66_1038.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_1038.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (lid) -> begin
Binding_lid ((lid, t))
end))

# 687 "FStar.TypeChecker.Env.fst"
let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))

# 689 "FStar.TypeChecker.Env.fst"
let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (
# 690 "FStar.TypeChecker.Env.fst"
let _66_1048 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (
# 691 "FStar.TypeChecker.Env.fst"
let _66_1050 = env
in {solver = _66_1050.solver; range = _66_1050.range; curmodule = _66_1050.curmodule; gamma = []; gamma_cache = _66_1050.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _66_1050.sigtab; is_pattern = _66_1050.is_pattern; instantiate_imp = _66_1050.instantiate_imp; effects = _66_1050.effects; generalize = _66_1050.generalize; letrecs = _66_1050.letrecs; top_level = _66_1050.top_level; check_uvars = _66_1050.check_uvars; use_eq = _66_1050.use_eq; is_iface = _66_1050.is_iface; admit = _66_1050.admit; default_effects = _66_1050.default_effects; type_of = _66_1050.type_of; universe_of = _66_1050.universe_of; use_bv_sorts = _66_1050.use_bv_sorts})))

# 696 "FStar.TypeChecker.Env.fst"
let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))

# 699 "FStar.TypeChecker.Env.fst"
let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (
# 700 "FStar.TypeChecker.Env.fst"
let _66_1058 = env
in {solver = _66_1058.solver; range = _66_1058.range; curmodule = _66_1058.curmodule; gamma = _66_1058.gamma; gamma_cache = _66_1058.gamma_cache; modules = _66_1058.modules; expected_typ = Some (t); sigtab = _66_1058.sigtab; is_pattern = _66_1058.is_pattern; instantiate_imp = _66_1058.instantiate_imp; effects = _66_1058.effects; generalize = _66_1058.generalize; letrecs = _66_1058.letrecs; top_level = _66_1058.top_level; check_uvars = _66_1058.check_uvars; use_eq = false; is_iface = _66_1058.is_iface; admit = _66_1058.admit; default_effects = _66_1058.default_effects; type_of = _66_1058.type_of; universe_of = _66_1058.universe_of; use_bv_sorts = _66_1058.use_bv_sorts}))

# 702 "FStar.TypeChecker.Env.fst"
let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

# 706 "FStar.TypeChecker.Env.fst"
let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _145_1023 = (expected_typ env)
in ((
# 707 "FStar.TypeChecker.Env.fst"
let _66_1065 = env
in {solver = _66_1065.solver; range = _66_1065.range; curmodule = _66_1065.curmodule; gamma = _66_1065.gamma; gamma_cache = _66_1065.gamma_cache; modules = _66_1065.modules; expected_typ = None; sigtab = _66_1065.sigtab; is_pattern = _66_1065.is_pattern; instantiate_imp = _66_1065.instantiate_imp; effects = _66_1065.effects; generalize = _66_1065.generalize; letrecs = _66_1065.letrecs; top_level = _66_1065.top_level; check_uvars = _66_1065.check_uvars; use_eq = false; is_iface = _66_1065.is_iface; admit = _66_1065.admit; default_effects = _66_1065.default_effects; type_of = _66_1065.type_of; universe_of = _66_1065.universe_of; use_bv_sorts = _66_1065.use_bv_sorts}), _145_1023)))

# 709 "FStar.TypeChecker.Env.fst"
let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (
# 710 "FStar.TypeChecker.Env.fst"
let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (
# 712 "FStar.TypeChecker.Env.fst"
let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(FStar_All.pipe_right env.gamma (FStar_List.collect (fun _66_10 -> (match (_66_10) with
| Binding_sig (_66_1072, se) -> begin
(se)::[]
end
| _66_1077 -> begin
[]
end))))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (
# 718 "FStar.TypeChecker.Env.fst"
let _66_1079 = (add_sigelts env sigs)
in (
# 719 "FStar.TypeChecker.Env.fst"
let _66_1081 = (FStar_Util.smap_clear env.gamma_cache)
in (
# 720 "FStar.TypeChecker.Env.fst"
let _66_1083 = env
in {solver = _66_1083.solver; range = _66_1083.range; curmodule = empty_lid; gamma = []; gamma_cache = _66_1083.gamma_cache; modules = (m)::env.modules; expected_typ = _66_1083.expected_typ; sigtab = _66_1083.sigtab; is_pattern = _66_1083.is_pattern; instantiate_imp = _66_1083.instantiate_imp; effects = _66_1083.effects; generalize = _66_1083.generalize; letrecs = _66_1083.letrecs; top_level = _66_1083.top_level; check_uvars = _66_1083.check_uvars; use_eq = _66_1083.use_eq; is_iface = _66_1083.is_iface; admit = _66_1083.admit; default_effects = _66_1083.default_effects; type_of = _66_1083.type_of; universe_of = _66_1083.universe_of; use_bv_sorts = _66_1083.use_bv_sorts}))))))

# 728 "FStar.TypeChecker.Env.fst"
let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (
# 729 "FStar.TypeChecker.Env.fst"
let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (
# 730 "FStar.TypeChecker.Env.fst"
let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (
# 731 "FStar.TypeChecker.Env.fst"
let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| Binding_univ (_66_1096)::tl -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _145_1040 = (let _145_1039 = (FStar_Syntax_Free.uvars t)
in (ext out _145_1039))
in (aux _145_1040 tl))
end
| (Binding_sig (_)::_) | (Binding_sig_inst (_)::_) -> begin
out
end))
in (aux no_uvs env.gamma)))))

# 740 "FStar.TypeChecker.Env.fst"
let univ_vars : env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun env -> (
# 741 "FStar.TypeChecker.Env.fst"
let no_univs = FStar_Syntax_Syntax.no_universe_uvars
in (
# 742 "FStar.TypeChecker.Env.fst"
let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (
# 743 "FStar.TypeChecker.Env.fst"
let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_sig_inst (_)::tl) | (Binding_univ (_)::tl) -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _145_1052 = (let _145_1051 = (FStar_Syntax_Free.univs t)
in (ext out _145_1051))
in (aux _145_1052 tl))
end
| Binding_sig (_66_1166)::_66_1164 -> begin
out
end))
in (aux no_univs env.gamma)))))

# 752 "FStar.TypeChecker.Env.fst"
let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _66_11 -> (match (_66_11) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))

# 760 "FStar.TypeChecker.Env.fst"
let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _145_1059 = (let _145_1058 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _145_1058 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _145_1059 FStar_List.rev)))

# 762 "FStar.TypeChecker.Env.fst"
let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))

# 764 "FStar.TypeChecker.Env.fst"
let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))

# 766 "FStar.TypeChecker.Env.fst"
let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))

# 768 "FStar.TypeChecker.Env.fst"
let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (
# 769 "FStar.TypeChecker.Env.fst"
let keys = (FStar_List.fold_left (fun keys _66_12 -> (match (_66_12) with
| Binding_sig (lids, _66_1198) -> begin
(FStar_List.append lids keys)
end
| _66_1202 -> begin
keys
end)) [] env.gamma)
in (let _145_1083 = (sigtab env)
in (FStar_Util.smap_fold _145_1083 (fun _66_1204 v keys -> (let _145_1082 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _145_1082 keys))) keys))))

# 776 "FStar.TypeChecker.Env.fst"
let dummy_solver : solver_t = {init = (fun _66_1208 -> ()); push = (fun _66_1210 -> ()); pop = (fun _66_1212 -> ()); mark = (fun _66_1214 -> ()); reset_mark = (fun _66_1216 -> ()); commit_mark = (fun _66_1218 -> ()); encode_modul = (fun _66_1220 _66_1222 -> ()); encode_sig = (fun _66_1224 _66_1226 -> ()); solve = (fun _66_1228 _66_1230 -> ()); is_trivial = (fun _66_1232 _66_1234 -> false); finish = (fun _66_1236 -> ()); refresh = (fun _66_1237 -> ())}

# 791 "FStar.TypeChecker.Env.fst"
let no_solver_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t))  ->  env = (fun tc -> (let _145_1112 = (FStar_Ident.lid_of_path (("dummy")::[]) FStar_Range.dummyRange)
in (initial_env tc dummy_solver _145_1112)))




