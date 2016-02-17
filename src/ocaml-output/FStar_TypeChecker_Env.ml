
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
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ Prims.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap Prims.list; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; default_effects : (FStar_Ident.lident * FStar_Ident.lident) Prims.list; type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t); use_bv_sorts : Prims.bool} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit; solve : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit} 
 and guard_t =
{guard_f : FStar_TypeChecker_Common.guard_formula; deferred : FStar_TypeChecker_Common.deferred; univ_ineqs : FStar_TypeChecker_Common.univ_ineq Prims.list; implicits : (env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list}

# 55 "FStar.TypeChecker.Env.fst"
let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

# 78 "FStar.TypeChecker.Env.fst"
let is_Mksolver_t : solver_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksolver_t"))))

# 92 "FStar.TypeChecker.Env.fst"
let is_Mkguard_t : guard_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkguard_t"))))

# 98 "FStar.TypeChecker.Env.fst"
type env_t =
env

# 99 "FStar.TypeChecker.Env.fst"
type implicits =
(env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list

# 101 "FStar.TypeChecker.Env.fst"
type sigtable =
FStar_Syntax_Syntax.sigelt FStar_Util.smap

# 161 "FStar.TypeChecker.Env.fst"
let visible_at : delta_level  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun d q -> (match ((d, q)) with
| ((NoDelta, _)) | ((OnlyInline, FStar_Syntax_Syntax.Inline)) | ((Unfold, FStar_Syntax_Syntax.Inline)) | ((Unfold, FStar_Syntax_Syntax.Unfoldable)) -> begin
true
end
| _66_93 -> begin
false
end))

# 168 "FStar.TypeChecker.Env.fst"
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

# 176 "FStar.TypeChecker.Env.fst"
let default_table_size : Prims.int = 200

# 177 "FStar.TypeChecker.Env.fst"
let new_sigtab = (fun _66_115 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))

# 179 "FStar.TypeChecker.Env.fst"
let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t))  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun tc solver module_lid -> (let _145_359 = (FStar_Util.smap_create 100)
in (let _145_358 = (let _145_357 = (new_sigtab ())
in (_145_357)::[])
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _145_359; modules = []; expected_typ = None; sigtab = _145_358; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []; type_of = tc; use_bv_sorts = false})))

# 204 "FStar.TypeChecker.Env.fst"
let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> (FStar_List.hd env.sigtab))

# 205 "FStar.TypeChecker.Env.fst"
let push : env  ->  Prims.string  ->  env = (fun env msg -> (
# 206 "FStar.TypeChecker.Env.fst"
let _66_122 = (env.solver.push msg)
in (
# 207 "FStar.TypeChecker.Env.fst"
let _66_124 = env
in (let _145_368 = (let _145_367 = (let _145_366 = (sigtab env)
in (FStar_Util.smap_copy _145_366))
in (_145_367)::env.sigtab)
in {solver = _66_124.solver; range = _66_124.range; curmodule = _66_124.curmodule; gamma = _66_124.gamma; gamma_cache = _66_124.gamma_cache; modules = _66_124.modules; expected_typ = _66_124.expected_typ; sigtab = _145_368; is_pattern = _66_124.is_pattern; instantiate_imp = _66_124.instantiate_imp; effects = _66_124.effects; generalize = _66_124.generalize; letrecs = _66_124.letrecs; top_level = _66_124.top_level; check_uvars = _66_124.check_uvars; use_eq = _66_124.use_eq; is_iface = _66_124.is_iface; admit = _66_124.admit; default_effects = _66_124.default_effects; type_of = _66_124.type_of; use_bv_sorts = _66_124.use_bv_sorts}))))

# 208 "FStar.TypeChecker.Env.fst"
let mark : env  ->  env = (fun env -> (
# 209 "FStar.TypeChecker.Env.fst"
let _66_127 = (env.solver.mark "USER MARK")
in (
# 210 "FStar.TypeChecker.Env.fst"
let _66_129 = env
in (let _145_373 = (let _145_372 = (let _145_371 = (sigtab env)
in (FStar_Util.smap_copy _145_371))
in (_145_372)::env.sigtab)
in {solver = _66_129.solver; range = _66_129.range; curmodule = _66_129.curmodule; gamma = _66_129.gamma; gamma_cache = _66_129.gamma_cache; modules = _66_129.modules; expected_typ = _66_129.expected_typ; sigtab = _145_373; is_pattern = _66_129.is_pattern; instantiate_imp = _66_129.instantiate_imp; effects = _66_129.effects; generalize = _66_129.generalize; letrecs = _66_129.letrecs; top_level = _66_129.top_level; check_uvars = _66_129.check_uvars; use_eq = _66_129.use_eq; is_iface = _66_129.is_iface; admit = _66_129.admit; default_effects = _66_129.default_effects; type_of = _66_129.type_of; use_bv_sorts = _66_129.use_bv_sorts}))))

# 211 "FStar.TypeChecker.Env.fst"
let commit_mark : env  ->  env = (fun env -> (
# 212 "FStar.TypeChecker.Env.fst"
let _66_132 = (env.solver.commit_mark "USER MARK")
in (
# 213 "FStar.TypeChecker.Env.fst"
let sigtab = (match (env.sigtab) with
| hd::_66_136::tl -> begin
(hd)::tl
end
| _66_141 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 216 "FStar.TypeChecker.Env.fst"
let _66_143 = env
in {solver = _66_143.solver; range = _66_143.range; curmodule = _66_143.curmodule; gamma = _66_143.gamma; gamma_cache = _66_143.gamma_cache; modules = _66_143.modules; expected_typ = _66_143.expected_typ; sigtab = sigtab; is_pattern = _66_143.is_pattern; instantiate_imp = _66_143.instantiate_imp; effects = _66_143.effects; generalize = _66_143.generalize; letrecs = _66_143.letrecs; top_level = _66_143.top_level; check_uvars = _66_143.check_uvars; use_eq = _66_143.use_eq; is_iface = _66_143.is_iface; admit = _66_143.admit; default_effects = _66_143.default_effects; type_of = _66_143.type_of; use_bv_sorts = _66_143.use_bv_sorts}))))

# 217 "FStar.TypeChecker.Env.fst"
let reset_mark : env  ->  env = (fun env -> (
# 218 "FStar.TypeChecker.Env.fst"
let _66_146 = (env.solver.reset_mark "USER MARK")
in (
# 219 "FStar.TypeChecker.Env.fst"
let _66_148 = env
in (let _145_378 = (FStar_List.tl env.sigtab)
in {solver = _66_148.solver; range = _66_148.range; curmodule = _66_148.curmodule; gamma = _66_148.gamma; gamma_cache = _66_148.gamma_cache; modules = _66_148.modules; expected_typ = _66_148.expected_typ; sigtab = _145_378; is_pattern = _66_148.is_pattern; instantiate_imp = _66_148.instantiate_imp; effects = _66_148.effects; generalize = _66_148.generalize; letrecs = _66_148.letrecs; top_level = _66_148.top_level; check_uvars = _66_148.check_uvars; use_eq = _66_148.use_eq; is_iface = _66_148.is_iface; admit = _66_148.admit; default_effects = _66_148.default_effects; type_of = _66_148.type_of; use_bv_sorts = _66_148.use_bv_sorts}))))

# 220 "FStar.TypeChecker.Env.fst"
let pop : env  ->  Prims.string  ->  env = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(FStar_All.failwith "Too many pops")
end
| _66_158::tl -> begin
(
# 224 "FStar.TypeChecker.Env.fst"
let _66_160 = (env.solver.pop msg)
in (
# 225 "FStar.TypeChecker.Env.fst"
let _66_162 = env
in {solver = _66_162.solver; range = _66_162.range; curmodule = _66_162.curmodule; gamma = _66_162.gamma; gamma_cache = _66_162.gamma_cache; modules = _66_162.modules; expected_typ = _66_162.expected_typ; sigtab = tl; is_pattern = _66_162.is_pattern; instantiate_imp = _66_162.instantiate_imp; effects = _66_162.effects; generalize = _66_162.generalize; letrecs = _66_162.letrecs; top_level = _66_162.top_level; check_uvars = _66_162.check_uvars; use_eq = _66_162.use_eq; is_iface = _66_162.is_iface; admit = _66_162.admit; default_effects = _66_162.default_effects; type_of = _66_162.type_of; use_bv_sorts = _66_162.use_bv_sorts}))
end))

# 230 "FStar.TypeChecker.Env.fst"
let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> ((let _145_388 = (FStar_ST.read FStar_Options.debug)
in (FStar_All.pipe_right _145_388 (FStar_Util.for_some (fun x -> ((env.curmodule.FStar_Ident.str = "") || (env.curmodule.FStar_Ident.str = x)))))) && (FStar_Options.debug_level_geq l)))

# 233 "FStar.TypeChecker.Env.fst"
let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(
# 233 "FStar.TypeChecker.Env.fst"
let _66_169 = e
in {solver = _66_169.solver; range = r; curmodule = _66_169.curmodule; gamma = _66_169.gamma; gamma_cache = _66_169.gamma_cache; modules = _66_169.modules; expected_typ = _66_169.expected_typ; sigtab = _66_169.sigtab; is_pattern = _66_169.is_pattern; instantiate_imp = _66_169.instantiate_imp; effects = _66_169.effects; generalize = _66_169.generalize; letrecs = _66_169.letrecs; top_level = _66_169.top_level; check_uvars = _66_169.check_uvars; use_eq = _66_169.use_eq; is_iface = _66_169.is_iface; admit = _66_169.admit; default_effects = _66_169.default_effects; type_of = _66_169.type_of; use_bv_sorts = _66_169.use_bv_sorts})
end)

# 234 "FStar.TypeChecker.Env.fst"
let get_range : env  ->  FStar_Range.range = (fun e -> e.range)

# 239 "FStar.TypeChecker.Env.fst"
let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)

# 240 "FStar.TypeChecker.Env.fst"
let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)

# 241 "FStar.TypeChecker.Env.fst"
let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (
# 241 "FStar.TypeChecker.Env.fst"
let _66_176 = env
in {solver = _66_176.solver; range = _66_176.range; curmodule = lid; gamma = _66_176.gamma; gamma_cache = _66_176.gamma_cache; modules = _66_176.modules; expected_typ = _66_176.expected_typ; sigtab = _66_176.sigtab; is_pattern = _66_176.is_pattern; instantiate_imp = _66_176.instantiate_imp; effects = _66_176.effects; generalize = _66_176.generalize; letrecs = _66_176.letrecs; top_level = _66_176.top_level; check_uvars = _66_176.check_uvars; use_eq = _66_176.use_eq; is_iface = _66_176.is_iface; admit = _66_176.admit; default_effects = _66_176.default_effects; type_of = _66_176.type_of; use_bv_sorts = _66_176.use_bv_sorts}))

# 242 "FStar.TypeChecker.Env.fst"
let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))

# 243 "FStar.TypeChecker.Env.fst"
let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (let _145_412 = (sigtab env)
in (FStar_Util.smap_try_find _145_412 (FStar_Ident.text_of_lid lid))))

# 245 "FStar.TypeChecker.Env.fst"
let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))

# 248 "FStar.TypeChecker.Env.fst"
let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _145_417 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _145_417)))

# 252 "FStar.TypeChecker.Env.fst"
let new_u_univ = (fun _66_185 -> (let _145_419 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_145_419)))

# 255 "FStar.TypeChecker.Env.fst"
let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match ((ts, us)) with
| (([], t), []) -> begin
([], t)
end
| ((formals, t), _66_198) -> begin
(
# 259 "FStar.TypeChecker.Env.fst"
let _66_200 = ()
in (
# 260 "FStar.TypeChecker.Env.fst"
let n = ((FStar_List.length formals) - 1)
in (
# 261 "FStar.TypeChecker.Env.fst"
let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN (((n - i), u)))))
in (let _145_426 = (FStar_Syntax_Subst.subst vs t)
in (us, _145_426)))))
end))

# 265 "FStar.TypeChecker.Env.fst"
let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _66_1 -> (match (_66_1) with
| ([], t) -> begin
([], t)
end
| (us, t) -> begin
(
# 268 "FStar.TypeChecker.Env.fst"
let us' = (FStar_All.pipe_right us (FStar_List.map (fun _66_213 -> (new_u_univ ()))))
in (inst_tscheme_with (us, t) us'))
end))

# 271 "FStar.TypeChecker.Env.fst"
let inst_effect_fun : env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun env ed _66_220 -> (match (_66_220) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(let _145_436 = (inst_tscheme ((FStar_List.append ed.FStar_Syntax_Syntax.univs us), t))
in (Prims.snd _145_436))
end
| _66_223 -> begin
(let _145_438 = (let _145_437 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _145_437))
in (FStar_All.failwith _145_438))
end)
end))

# 276 "FStar.TypeChecker.Env.fst"
type tri =
| Yes
| No
| Maybe

# 277 "FStar.TypeChecker.Env.fst"
let is_Yes = (fun _discr_ -> (match (_discr_) with
| Yes (_) -> begin
true
end
| _ -> begin
false
end))

# 278 "FStar.TypeChecker.Env.fst"
let is_No = (fun _discr_ -> (match (_discr_) with
| No (_) -> begin
true
end
| _ -> begin
false
end))

# 279 "FStar.TypeChecker.Env.fst"
let is_Maybe = (fun _discr_ -> (match (_discr_) with
| Maybe (_) -> begin
true
end
| _ -> begin
false
end))

# 281 "FStar.TypeChecker.Env.fst"
let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (
# 282 "FStar.TypeChecker.Env.fst"
let cur = (current_module env)
in if (l.FStar_Ident.nsstr = cur.FStar_Ident.str) then begin
Yes
end else begin
if (FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str) then begin
(
# 285 "FStar.TypeChecker.Env.fst"
let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (
# 286 "FStar.TypeChecker.Env.fst"
let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (
# 287 "FStar.TypeChecker.Env.fst"
let rec aux = (fun c l -> (match ((c, l)) with
| ([], _66_234) -> begin
Maybe
end
| (_66_237, []) -> begin
No
end
| (hd::tl, hd'::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _66_248 -> begin
No
end))
in (aux cur lns))))
end else begin
No
end
end))

# 295 "FStar.TypeChecker.Env.fst"
let lookup_qname : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either Prims.option = (fun env lid -> (
# 296 "FStar.TypeChecker.Env.fst"
let cur_mod = (in_cur_mod env lid)
in (
# 297 "FStar.TypeChecker.Env.fst"
let cache = (fun t -> (
# 297 "FStar.TypeChecker.Env.fst"
let _66_254 = (FStar_Util.smap_add env.gamma_cache lid.FStar_Ident.str t)
in Some (t)))
in (
# 298 "FStar.TypeChecker.Env.fst"
let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find env.gamma_cache lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _66_2 -> (match (_66_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _145_458 = (let _145_457 = (inst_tscheme t)
in FStar_Util.Inl (_145_457))
in Some (_145_458))
end else begin
None
end
end
| Binding_sig (_66_263, FStar_Syntax_Syntax.Sig_bundle (ses, _66_266, _66_268, _66_270)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _145_460 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _145_460 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr ((se, None))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(
# 309 "FStar.TypeChecker.Env.fst"
let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_66_283) -> begin
Some (t)
end
| _66_286 -> begin
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
| _66_293 -> begin
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

# 326 "FStar.TypeChecker.Env.fst"
let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _66_303, _66_305, _66_307) -> begin
(add_sigelts env ses)
end
| _66_311 -> begin
(
# 329 "FStar.TypeChecker.Env.fst"
let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _145_470 = (sigtab env)
in (FStar_Util.smap_add _145_470 l.FStar_Ident.str se))) lids))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))

# 338 "FStar.TypeChecker.Env.fst"
let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun _66_3 -> (match (_66_3) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _66_322 -> begin
None
end))))

# 344 "FStar.TypeChecker.Env.fst"
let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _66_4 -> (match (_66_4) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _66_329 -> begin
false
end)) env.gamma) FStar_Option.isSome))

# 350 "FStar.TypeChecker.Env.fst"
let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_66_333, lb::[]), _66_338, _66_340, _66_342) -> begin
(let _145_490 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_145_490))
end
| FStar_Syntax_Syntax.Sig_let ((_66_346, lbs), _66_350, _66_352, _66_354) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_66_359) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (lid') -> begin
if (FStar_Ident.lid_equals lid lid') then begin
(let _145_492 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_145_492))
end else begin
None
end
end)))
end
| _66_364 -> begin
None
end))

# 364 "FStar.TypeChecker.Env.fst"
let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _145_500 = (let _145_499 = (let _145_498 = (variable_not_found bv)
in (let _145_497 = (FStar_Syntax_Syntax.range_of_bv bv)
in (_145_498, _145_497)))
in FStar_Syntax_Syntax.Error (_145_499))
in (Prims.raise _145_500))
end
| Some (t) -> begin
t
end))

# 369 "FStar.TypeChecker.Env.fst"
let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _66_373) -> begin
(let _145_506 = (let _145_505 = (let _145_504 = (let _145_503 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _145_503))
in (ne.FStar_Syntax_Syntax.univs, _145_504))
in (inst_tscheme _145_505))
in Some (_145_506))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _66_380, _66_382, _66_384) -> begin
(let _145_510 = (let _145_509 = (let _145_508 = (let _145_507 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _145_507))
in (us, _145_508))
in (inst_tscheme _145_509))
in Some (_145_510))
end
| _66_388 -> begin
None
end))

# 379 "FStar.TypeChecker.Env.fst"
let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_66_398, t) -> begin
Some (t)
end)
end
| _66_403 -> begin
None
end))

# 388 "FStar.TypeChecker.Env.fst"
let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env lid -> (
# 389 "FStar.TypeChecker.Env.fst"
let mapper = (fun _66_5 -> (match (_66_5) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_66_410, uvs, t, _66_414, _66_416, _66_418, _66_420, _66_422), None) -> begin
(let _145_521 = (inst_tscheme (uvs, t))
in Some (_145_521))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _66_433), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _145_522 = (inst_tscheme (uvs, t))
in Some (_145_522))
end else begin
None
end
end else begin
(let _145_523 = (inst_tscheme (uvs, t))
in Some (_145_523))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _66_444, _66_446, _66_448, _66_450), None) -> begin
(match (tps) with
| [] -> begin
(let _145_525 = (inst_tscheme (uvs, k))
in (FStar_All.pipe_left (fun _145_524 -> Some (_145_524)) _145_525))
end
| _66_458 -> begin
(let _145_530 = (let _145_529 = (let _145_528 = (let _145_527 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _145_527))
in (uvs, _145_528))
in (inst_tscheme _145_529))
in (FStar_All.pipe_left (fun _145_526 -> Some (_145_526)) _145_530))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _66_464, _66_466, _66_468, _66_470), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _145_532 = (inst_tscheme_with (uvs, k) us)
in (FStar_All.pipe_left (fun _145_531 -> Some (_145_531)) _145_532))
end
| _66_479 -> begin
(let _145_537 = (let _145_536 = (let _145_535 = (let _145_534 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _145_534))
in (uvs, _145_535))
in (inst_tscheme_with _145_536 us))
in (FStar_All.pipe_left (fun _145_533 -> Some (_145_533)) _145_537))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_66_483), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _66_488 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _145_538 = (lookup_qname env lid)
in (FStar_Util.bind_opt _145_538 mapper))) with
| Some (us, t) -> begin
Some ((us, (
# 423 "FStar.TypeChecker.Env.fst"
let _66_494 = t
in {FStar_Syntax_Syntax.n = _66_494.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _66_494.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _66_494.FStar_Syntax_Syntax.vars})))
end
| None -> begin
None
end)))

# 426 "FStar.TypeChecker.Env.fst"
let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _145_545 = (let _145_544 = (let _145_543 = (name_not_found l)
in (_145_543, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_145_544))
in (Prims.raise _145_545))
end
| Some (x) -> begin
x
end))

# 431 "FStar.TypeChecker.Env.fst"
let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_66_505, uvs, t, _66_509, _66_511), None)) -> begin
(inst_tscheme (uvs, t))
end
| _66_519 -> begin
(let _145_552 = (let _145_551 = (let _145_550 = (name_not_found lid)
in (_145_550, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_145_551))
in (Prims.raise _145_552))
end))

# 436 "FStar.TypeChecker.Env.fst"
let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_66_523, uvs, t, _66_527, _66_529, _66_531, _66_533, _66_535), None)) -> begin
(inst_tscheme (uvs, t))
end
| _66_543 -> begin
(let _145_559 = (let _145_558 = (let _145_557 = (name_not_found lid)
in (_145_557, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_145_558))
in (Prims.raise _145_559))
end))

# 441 "FStar.TypeChecker.Env.fst"
let lookup_definition : delta_level  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_66_553, lbs), _66_557, _66_559, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (
# 447 "FStar.TypeChecker.Env.fst"
let lid' = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Ident.lid_equals lid lid') then begin
(let _145_568 = (let _145_567 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (lb.FStar_Syntax_Syntax.lbunivs, _145_567))
in Some (_145_568))
end else begin
None
end)))
end
| _66_566 -> begin
None
end)
end
| _66_568 -> begin
None
end))

# 455 "FStar.TypeChecker.Env.fst"
let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _145_575 = (let _145_574 = (let _145_573 = (name_not_found ftv)
in (_145_573, (FStar_Ident.range_of_lid ftv)))
in FStar_Syntax_Syntax.Error (_145_574))
in (Prims.raise _145_575))
end
| Some (k) -> begin
k
end))

# 460 "FStar.TypeChecker.Env.fst"
let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (
# 461 "FStar.TypeChecker.Env.fst"
let fail = (fun _66_578 -> (match (()) with
| () -> begin
(let _145_586 = (let _145_585 = (FStar_Util.string_of_int i)
in (let _145_584 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _145_585 _145_584)))
in (FStar_All.failwith _145_586))
end))
in (
# 462 "FStar.TypeChecker.Env.fst"
let _66_582 = (lookup_datacon env lid)
in (match (_66_582) with
| (_66_580, t) -> begin
(match ((let _145_587 = (FStar_Syntax_Subst.compress t)
in _145_587.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _66_585) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(
# 467 "FStar.TypeChecker.Env.fst"
let b = (FStar_List.nth binders i)
in (let _145_588 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _145_588 Prims.fst)))
end
end
| _66_590 -> begin
(fail ())
end)
end))))

# 471 "FStar.TypeChecker.Env.fst"
let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_66_594, uvs, t, q, _66_599), None)) -> begin
Some (((uvs, t), q))
end
| _66_607 -> begin
None
end))

# 476 "FStar.TypeChecker.Env.fst"
let lookup_effect_abbrev : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _66_616), None)) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _66_6 -> (match (_66_6) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _66_626 -> begin
false
end)))) then begin
None
end else begin
(
# 481 "FStar.TypeChecker.Env.fst"
let _66_631 = (FStar_Syntax_Util.open_univ_vars_binders_and_comp univs binders c)
in (match (_66_631) with
| (_66_628, binders, c) -> begin
Some ((binders, c))
end))
end
end
| _66_633 -> begin
None
end))

# 485 "FStar.TypeChecker.Env.fst"
let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_66_637, _66_639, _66_641, _66_643, _66_645, dcs, _66_648, _66_650), _66_654)) -> begin
dcs
end
| _66_659 -> begin
[]
end))

# 490 "FStar.TypeChecker.Env.fst"
let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_66_663, _66_665, _66_667, l, _66_670, _66_672, _66_674, _66_676), _66_680)) -> begin
l
end
| _66_685 -> begin
(let _145_607 = (let _145_606 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _145_606))
in (FStar_All.failwith _145_607))
end))

# 495 "FStar.TypeChecker.Env.fst"
let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_66_689, _66_691, _66_693, _66_695, _66_697, _66_699, _66_701, _66_703), _66_707)) -> begin
true
end
| _66_712 -> begin
false
end))

# 500 "FStar.TypeChecker.Env.fst"
let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_66_716, _66_718, _66_720, _66_722, _66_724, _66_726, tags, _66_729), _66_733)) -> begin
(FStar_Util.for_some (fun _66_7 -> (match (_66_7) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _66_745 -> begin
false
end)) tags)
end
| _66_747 -> begin
false
end))

# 506 "FStar.TypeChecker.Env.fst"
let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_66_751, _66_753, _66_755, quals, _66_758), _66_762)) -> begin
(FStar_Util.for_some (fun _66_8 -> (match (_66_8) with
| FStar_Syntax_Syntax.Projector (_66_768) -> begin
true
end
| _66_771 -> begin
false
end)) quals)
end
| _66_773 -> begin
false
end))

# 515 "FStar.TypeChecker.Env.fst"
let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))

# 518 "FStar.TypeChecker.Env.fst"
let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _145_633 = (let _145_632 = (let _145_631 = (name_not_found l)
in (_145_631, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_145_632))
in (Prims.raise _145_633))
end
| Some (md) -> begin
md
end))

# 523 "FStar.TypeChecker.Env.fst"
let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
(l1, (fun t wp -> wp), (fun t wp -> wp))
end else begin
if (((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid))) then begin
(FStar_Syntax_Const.effect_GTot_lid, (fun t wp -> wp), (fun t wp -> wp))
end else begin
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _66_801 -> (match (_66_801) with
| (m1, m2, _66_796, _66_798, _66_800) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _145_709 = (let _145_708 = (let _145_707 = (let _145_706 = (FStar_Syntax_Print.lid_to_string l1)
in (let _145_705 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _145_706 _145_705)))
in (_145_707, env.range))
in FStar_Syntax_Syntax.Error (_145_708))
in (Prims.raise _145_709))
end
| Some (_66_804, _66_806, m3, j1, j2) -> begin
(m3, j1, j2)
end)
end
end)

# 533 "FStar.TypeChecker.Env.fst"
let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge Prims.option = (fun env l1 l2 -> if ((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid))) then begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end else begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end)

# 539 "FStar.TypeChecker.Env.fst"
let wp_sig_aux : FStar_Syntax_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun decls m -> (match ((FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))))) with
| None -> begin
(let _145_724 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _145_724))
end
| Some (md) -> begin
(
# 543 "FStar.TypeChecker.Env.fst"
let _66_827 = (inst_tscheme (md.FStar_Syntax_Syntax.univs, md.FStar_Syntax_Syntax.signature))
in (match (_66_827) with
| (_66_825, s) -> begin
(
# 544 "FStar.TypeChecker.Env.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match ((md.FStar_Syntax_Syntax.binders, s.FStar_Syntax_Syntax.n)) with
| ([], FStar_Syntax_Syntax.Tm_arrow ((a, _66_840)::(wp, _66_836)::(wlp, _66_832)::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _66_848 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))

# 549 "FStar.TypeChecker.Env.fst"
let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))

# 551 "FStar.TypeChecker.Env.fst"
let default_effect : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (FStar_Util.find_map env.default_effects (fun _66_855 -> (match (_66_855) with
| (l', m) -> begin
if (FStar_Ident.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))

# 553 "FStar.TypeChecker.Env.fst"
let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, _66_860, _66_862, c, quals, r) -> begin
(match ((FStar_Util.find_map quals (fun _66_9 -> (match (_66_9) with
| FStar_Syntax_Syntax.DefaultEffect (n) -> begin
n
end
| _66_872 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(
# 557 "FStar.TypeChecker.Env.fst"
let _66_876 = env
in {solver = _66_876.solver; range = _66_876.range; curmodule = _66_876.curmodule; gamma = _66_876.gamma; gamma_cache = _66_876.gamma_cache; modules = _66_876.modules; expected_typ = _66_876.expected_typ; sigtab = _66_876.sigtab; is_pattern = _66_876.is_pattern; instantiate_imp = _66_876.instantiate_imp; effects = _66_876.effects; generalize = _66_876.generalize; letrecs = _66_876.letrecs; top_level = _66_876.top_level; check_uvars = _66_876.check_uvars; use_eq = _66_876.use_eq; is_iface = _66_876.is_iface; admit = _66_876.admit; default_effects = ((e, l))::env.default_effects; type_of = _66_876.type_of; use_bv_sorts = _66_876.use_bv_sorts})
end)
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _66_880) -> begin
(
# 560 "FStar.TypeChecker.Env.fst"
let effects = (
# 560 "FStar.TypeChecker.Env.fst"
let _66_883 = env.effects
in {decls = (ne)::env.effects.decls; order = _66_883.order; joins = _66_883.joins})
in (
# 561 "FStar.TypeChecker.Env.fst"
let _66_886 = env
in {solver = _66_886.solver; range = _66_886.range; curmodule = _66_886.curmodule; gamma = _66_886.gamma; gamma_cache = _66_886.gamma_cache; modules = _66_886.modules; expected_typ = _66_886.expected_typ; sigtab = _66_886.sigtab; is_pattern = _66_886.is_pattern; instantiate_imp = _66_886.instantiate_imp; effects = effects; generalize = _66_886.generalize; letrecs = _66_886.letrecs; top_level = _66_886.top_level; check_uvars = _66_886.check_uvars; use_eq = _66_886.use_eq; is_iface = _66_886.is_iface; admit = _66_886.admit; default_effects = _66_886.default_effects; type_of = _66_886.type_of; use_bv_sorts = _66_886.use_bv_sorts}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _66_890) -> begin
(
# 564 "FStar.TypeChecker.Env.fst"
let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _145_745 = (e1.mlift r wp1)
in (e2.mlift r _145_745)))})
in (
# 569 "FStar.TypeChecker.Env.fst"
let mk_lift = (fun lift_t r wp1 -> (
# 570 "FStar.TypeChecker.Env.fst"
let _66_905 = (inst_tscheme lift_t)
in (match (_66_905) with
| (_66_903, lift_t) -> begin
(let _145_757 = (let _145_756 = (let _145_755 = (let _145_754 = (FStar_Syntax_Syntax.as_arg r)
in (let _145_753 = (let _145_752 = (FStar_Syntax_Syntax.as_arg wp1)
in (_145_752)::[])
in (_145_754)::_145_753))
in (lift_t, _145_755))
in FStar_Syntax_Syntax.Tm_app (_145_756))
in (FStar_Syntax_Syntax.mk _145_757 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (
# 573 "FStar.TypeChecker.Env.fst"
let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub.FStar_Syntax_Syntax.lift)}
in (
# 577 "FStar.TypeChecker.Env.fst"
let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (
# 582 "FStar.TypeChecker.Env.fst"
let print_mlift = (fun l -> (
# 583 "FStar.TypeChecker.Env.fst"
let arg = (let _145_774 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _145_774 None))
in (
# 584 "FStar.TypeChecker.Env.fst"
let wp = (let _145_775 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _145_775 None))
in (let _145_776 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _145_776)))))
in (
# 586 "FStar.TypeChecker.Env.fst"
let order = (edge)::env.effects.order
in (
# 588 "FStar.TypeChecker.Env.fst"
let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (
# 590 "FStar.TypeChecker.Env.fst"
let find_edge = (fun order _66_922 -> (match (_66_922) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _145_782 -> Some (_145_782)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (
# 599 "FStar.TypeChecker.Env.fst"
let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _145_790 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _145_789 = (find_edge order (i, k))
in (let _145_788 = (find_edge order (k, j))
in (_145_789, _145_788)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _66_934 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _145_790))) order))
in (
# 610 "FStar.TypeChecker.Env.fst"
let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (
# 612 "FStar.TypeChecker.Env.fst"
let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (
# 615 "FStar.TypeChecker.Env.fst"
let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _145_882 = (find_edge order (i, k))
in (let _145_881 = (find_edge order (j, k))
in (_145_882, _145_881)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _66_951, _66_953) -> begin
if ((let _145_883 = (find_edge order (k, ub))
in (FStar_Util.is_some _145_883)) && (not ((let _145_884 = (find_edge order (ub, k))
in (FStar_Util.is_some _145_884))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _66_957 -> begin
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
# 632 "FStar.TypeChecker.Env.fst"
let effects = (
# 632 "FStar.TypeChecker.Env.fst"
let _66_966 = env.effects
in {decls = _66_966.decls; order = order; joins = joins})
in (
# 635 "FStar.TypeChecker.Env.fst"
let _66_969 = env
in {solver = _66_969.solver; range = _66_969.range; curmodule = _66_969.curmodule; gamma = _66_969.gamma; gamma_cache = _66_969.gamma_cache; modules = _66_969.modules; expected_typ = _66_969.expected_typ; sigtab = _66_969.sigtab; is_pattern = _66_969.is_pattern; instantiate_imp = _66_969.instantiate_imp; effects = effects; generalize = _66_969.generalize; letrecs = _66_969.letrecs; top_level = _66_969.top_level; check_uvars = _66_969.check_uvars; use_eq = _66_969.use_eq; is_iface = _66_969.is_iface; admit = _66_969.admit; default_effects = _66_969.default_effects; type_of = _66_969.type_of; use_bv_sorts = _66_969.use_bv_sorts})))))))))))))
end
| _66_972 -> begin
env
end))

# 642 "FStar.TypeChecker.Env.fst"
let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (let _145_933 = (
# 642 "FStar.TypeChecker.Env.fst"
let _66_975 = env
in (let _145_932 = (let _145_931 = (let _145_930 = (let _145_929 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_145_929, s))
in Binding_sig (_145_930))
in (_145_931)::env.gamma)
in {solver = _66_975.solver; range = _66_975.range; curmodule = _66_975.curmodule; gamma = _145_932; gamma_cache = _66_975.gamma_cache; modules = _66_975.modules; expected_typ = _66_975.expected_typ; sigtab = _66_975.sigtab; is_pattern = _66_975.is_pattern; instantiate_imp = _66_975.instantiate_imp; effects = _66_975.effects; generalize = _66_975.generalize; letrecs = _66_975.letrecs; top_level = _66_975.top_level; check_uvars = _66_975.check_uvars; use_eq = _66_975.use_eq; is_iface = _66_975.is_iface; admit = _66_975.admit; default_effects = _66_975.default_effects; type_of = _66_975.type_of; use_bv_sorts = _66_975.use_bv_sorts}))
in (build_lattice _145_933 s)))

# 644 "FStar.TypeChecker.Env.fst"
let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (let _145_944 = (
# 644 "FStar.TypeChecker.Env.fst"
let _66_980 = env
in (let _145_943 = (let _145_942 = (let _145_941 = (let _145_940 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_145_940, s, us))
in Binding_sig_inst (_145_941))
in (_145_942)::env.gamma)
in {solver = _66_980.solver; range = _66_980.range; curmodule = _66_980.curmodule; gamma = _145_943; gamma_cache = _66_980.gamma_cache; modules = _66_980.modules; expected_typ = _66_980.expected_typ; sigtab = _66_980.sigtab; is_pattern = _66_980.is_pattern; instantiate_imp = _66_980.instantiate_imp; effects = _66_980.effects; generalize = _66_980.generalize; letrecs = _66_980.letrecs; top_level = _66_980.top_level; check_uvars = _66_980.check_uvars; use_eq = _66_980.use_eq; is_iface = _66_980.is_iface; admit = _66_980.admit; default_effects = _66_980.default_effects; type_of = _66_980.type_of; use_bv_sorts = _66_980.use_bv_sorts}))
in (build_lattice _145_944 s)))

# 646 "FStar.TypeChecker.Env.fst"
let push_local_binding : env  ->  binding  ->  env = (fun env b -> (
# 646 "FStar.TypeChecker.Env.fst"
let _66_984 = env
in {solver = _66_984.solver; range = _66_984.range; curmodule = _66_984.curmodule; gamma = (b)::env.gamma; gamma_cache = _66_984.gamma_cache; modules = _66_984.modules; expected_typ = _66_984.expected_typ; sigtab = _66_984.sigtab; is_pattern = _66_984.is_pattern; instantiate_imp = _66_984.instantiate_imp; effects = _66_984.effects; generalize = _66_984.generalize; letrecs = _66_984.letrecs; top_level = _66_984.top_level; check_uvars = _66_984.check_uvars; use_eq = _66_984.use_eq; is_iface = _66_984.is_iface; admit = _66_984.admit; default_effects = _66_984.default_effects; type_of = _66_984.type_of; use_bv_sorts = _66_984.use_bv_sorts}))

# 648 "FStar.TypeChecker.Env.fst"
let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))

# 650 "FStar.TypeChecker.Env.fst"
let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _66_994 -> (match (_66_994) with
| (x, _66_993) -> begin
(push_bv env x)
end)) env bs))

# 653 "FStar.TypeChecker.Env.fst"
let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(
# 655 "FStar.TypeChecker.Env.fst"
let _66_999 = ()
in (
# 656 "FStar.TypeChecker.Env.fst"
let x = (
# 656 "FStar.TypeChecker.Env.fst"
let _66_1001 = x
in {FStar_Syntax_Syntax.ppname = _66_1001.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_1001.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (lid) -> begin
Binding_lid ((lid, t))
end))

# 661 "FStar.TypeChecker.Env.fst"
let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))

# 663 "FStar.TypeChecker.Env.fst"
let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (
# 664 "FStar.TypeChecker.Env.fst"
let _66_1011 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (
# 665 "FStar.TypeChecker.Env.fst"
let _66_1013 = env
in {solver = _66_1013.solver; range = _66_1013.range; curmodule = _66_1013.curmodule; gamma = []; gamma_cache = _66_1013.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _66_1013.sigtab; is_pattern = _66_1013.is_pattern; instantiate_imp = _66_1013.instantiate_imp; effects = _66_1013.effects; generalize = _66_1013.generalize; letrecs = _66_1013.letrecs; top_level = _66_1013.top_level; check_uvars = _66_1013.check_uvars; use_eq = _66_1013.use_eq; is_iface = _66_1013.is_iface; admit = _66_1013.admit; default_effects = _66_1013.default_effects; type_of = _66_1013.type_of; use_bv_sorts = _66_1013.use_bv_sorts})))

# 670 "FStar.TypeChecker.Env.fst"
let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))

# 673 "FStar.TypeChecker.Env.fst"
let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (
# 674 "FStar.TypeChecker.Env.fst"
let _66_1021 = env
in {solver = _66_1021.solver; range = _66_1021.range; curmodule = _66_1021.curmodule; gamma = _66_1021.gamma; gamma_cache = _66_1021.gamma_cache; modules = _66_1021.modules; expected_typ = Some (t); sigtab = _66_1021.sigtab; is_pattern = _66_1021.is_pattern; instantiate_imp = _66_1021.instantiate_imp; effects = _66_1021.effects; generalize = _66_1021.generalize; letrecs = _66_1021.letrecs; top_level = _66_1021.top_level; check_uvars = _66_1021.check_uvars; use_eq = false; is_iface = _66_1021.is_iface; admit = _66_1021.admit; default_effects = _66_1021.default_effects; type_of = _66_1021.type_of; use_bv_sorts = _66_1021.use_bv_sorts}))

# 676 "FStar.TypeChecker.Env.fst"
let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

# 680 "FStar.TypeChecker.Env.fst"
let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _145_987 = (expected_typ env)
in ((
# 681 "FStar.TypeChecker.Env.fst"
let _66_1028 = env
in {solver = _66_1028.solver; range = _66_1028.range; curmodule = _66_1028.curmodule; gamma = _66_1028.gamma; gamma_cache = _66_1028.gamma_cache; modules = _66_1028.modules; expected_typ = None; sigtab = _66_1028.sigtab; is_pattern = _66_1028.is_pattern; instantiate_imp = _66_1028.instantiate_imp; effects = _66_1028.effects; generalize = _66_1028.generalize; letrecs = _66_1028.letrecs; top_level = _66_1028.top_level; check_uvars = _66_1028.check_uvars; use_eq = false; is_iface = _66_1028.is_iface; admit = _66_1028.admit; default_effects = _66_1028.default_effects; type_of = _66_1028.type_of; use_bv_sorts = _66_1028.use_bv_sorts}), _145_987)))

# 683 "FStar.TypeChecker.Env.fst"
let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (
# 684 "FStar.TypeChecker.Env.fst"
let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (
# 686 "FStar.TypeChecker.Env.fst"
let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(FStar_All.pipe_right env.gamma (FStar_List.collect (fun _66_10 -> (match (_66_10) with
| Binding_sig (_66_1035, se) -> begin
(se)::[]
end
| _66_1040 -> begin
[]
end))))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (
# 692 "FStar.TypeChecker.Env.fst"
let _66_1042 = (add_sigelts env sigs)
in (
# 693 "FStar.TypeChecker.Env.fst"
let _66_1044 = (FStar_Util.smap_clear env.gamma_cache)
in (
# 694 "FStar.TypeChecker.Env.fst"
let _66_1046 = env
in {solver = _66_1046.solver; range = _66_1046.range; curmodule = empty_lid; gamma = []; gamma_cache = _66_1046.gamma_cache; modules = (m)::env.modules; expected_typ = _66_1046.expected_typ; sigtab = _66_1046.sigtab; is_pattern = _66_1046.is_pattern; instantiate_imp = _66_1046.instantiate_imp; effects = _66_1046.effects; generalize = _66_1046.generalize; letrecs = _66_1046.letrecs; top_level = _66_1046.top_level; check_uvars = _66_1046.check_uvars; use_eq = _66_1046.use_eq; is_iface = _66_1046.is_iface; admit = _66_1046.admit; default_effects = _66_1046.default_effects; type_of = _66_1046.type_of; use_bv_sorts = _66_1046.use_bv_sorts}))))))

# 702 "FStar.TypeChecker.Env.fst"
let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (
# 703 "FStar.TypeChecker.Env.fst"
let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (
# 704 "FStar.TypeChecker.Env.fst"
let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (
# 705 "FStar.TypeChecker.Env.fst"
let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| Binding_univ (_66_1059)::tl -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _145_1004 = (let _145_1003 = (FStar_Syntax_Free.uvars t)
in (ext out _145_1003))
in (aux _145_1004 tl))
end
| (Binding_sig (_)::_) | (Binding_sig_inst (_)::_) -> begin
out
end))
in (aux no_uvs env.gamma)))))

# 714 "FStar.TypeChecker.Env.fst"
let univ_vars : env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun env -> (
# 715 "FStar.TypeChecker.Env.fst"
let no_univs = FStar_Syntax_Syntax.no_universe_uvars
in (
# 716 "FStar.TypeChecker.Env.fst"
let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (
# 717 "FStar.TypeChecker.Env.fst"
let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_sig_inst (_)::tl) | (Binding_univ (_)::tl) -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _145_1016 = (let _145_1015 = (FStar_Syntax_Free.univs t)
in (ext out _145_1015))
in (aux _145_1016 tl))
end
| Binding_sig (_66_1129)::_66_1127 -> begin
out
end))
in (aux no_univs env.gamma)))))

# 726 "FStar.TypeChecker.Env.fst"
let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _66_11 -> (match (_66_11) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))

# 734 "FStar.TypeChecker.Env.fst"
let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _145_1023 = (let _145_1022 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _145_1022 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _145_1023 FStar_List.rev)))

# 736 "FStar.TypeChecker.Env.fst"
let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))

# 738 "FStar.TypeChecker.Env.fst"
let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))

# 740 "FStar.TypeChecker.Env.fst"
let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))

# 742 "FStar.TypeChecker.Env.fst"
let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (
# 743 "FStar.TypeChecker.Env.fst"
let keys = (FStar_List.fold_left (fun keys _66_12 -> (match (_66_12) with
| Binding_sig (lids, _66_1161) -> begin
(FStar_List.append lids keys)
end
| _66_1165 -> begin
keys
end)) [] env.gamma)
in (let _145_1047 = (sigtab env)
in (FStar_Util.smap_fold _145_1047 (fun _66_1167 v keys -> (let _145_1046 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _145_1046 keys))) keys))))

# 750 "FStar.TypeChecker.Env.fst"
let dummy_solver : solver_t = {init = (fun _66_1171 -> ()); push = (fun _66_1173 -> ()); pop = (fun _66_1175 -> ()); mark = (fun _66_1177 -> ()); reset_mark = (fun _66_1179 -> ()); commit_mark = (fun _66_1181 -> ()); encode_modul = (fun _66_1183 _66_1185 -> ()); encode_sig = (fun _66_1187 _66_1189 -> ()); solve = (fun _66_1191 _66_1193 -> ()); is_trivial = (fun _66_1195 _66_1197 -> false); finish = (fun _66_1199 -> ()); refresh = (fun _66_1200 -> ())}

# 765 "FStar.TypeChecker.Env.fst"
let no_solver_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t))  ->  env = (fun tc -> (let _145_1076 = (FStar_Ident.lid_of_path (("dummy")::[]) FStar_Range.dummyRange)
in (initial_env tc dummy_solver _145_1076)))




