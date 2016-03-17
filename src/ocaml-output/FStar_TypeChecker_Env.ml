
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
let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_58_16) -> begin
_58_16
end))

# 32 "FStar.TypeChecker.Env.fst"
let ___Binding_lid____0 = (fun projectee -> (match (projectee) with
| Binding_lid (_58_19) -> begin
_58_19
end))

# 33 "FStar.TypeChecker.Env.fst"
let ___Binding_sig____0 = (fun projectee -> (match (projectee) with
| Binding_sig (_58_22) -> begin
_58_22
end))

# 34 "FStar.TypeChecker.Env.fst"
let ___Binding_univ____0 = (fun projectee -> (match (projectee) with
| Binding_univ (_58_25) -> begin
_58_25
end))

# 35 "FStar.TypeChecker.Env.fst"
let ___Binding_sig_inst____0 = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_58_28) -> begin
_58_28
end))

# 37 "FStar.TypeChecker.Env.fst"
type delta_level =
| NoDelta
| OnlyInline
| Unfold of FStar_Syntax_Syntax.delta_depth

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

# 40 "FStar.TypeChecker.Env.fst"
let ___Unfold____0 = (fun projectee -> (match (projectee) with
| Unfold (_58_31) -> begin
_58_31
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
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit; solve : (Prims.unit  ->  Prims.string) Prims.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit} 
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

# 165 "FStar.TypeChecker.Env.fst"
let visible_at : delta_level  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun d q -> (match ((d, q)) with
| ((NoDelta, _)) | ((OnlyInline, FStar_Syntax_Syntax.Inline)) | ((Unfold (_), FStar_Syntax_Syntax.Inline)) | ((Unfold (_), FStar_Syntax_Syntax.Unfoldable)) -> begin
true
end
| _58_102 -> begin
false
end))

# 172 "FStar.TypeChecker.Env.fst"
let glb_delta : delta_level  ->  delta_level  ->  delta_level = (fun d1 d2 -> (match ((d1, d2)) with
| ((NoDelta, _)) | ((_, NoDelta)) -> begin
NoDelta
end
| ((OnlyInline, _)) | ((_, OnlyInline)) -> begin
OnlyInline
end
| (Unfold (l1), Unfold (l2)) -> begin
(
# 178 "FStar.TypeChecker.Env.fst"
let rec aux = (fun l1 l2 -> (match ((l1, l2)) with
| ((FStar_Syntax_Syntax.Delta_constant, _)) | ((_, FStar_Syntax_Syntax.Delta_constant)) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| ((FStar_Syntax_Syntax.Delta_equational, l)) | ((l, FStar_Syntax_Syntax.Delta_equational)) -> begin
l
end
| (FStar_Syntax_Syntax.Delta_unfoldable (i), FStar_Syntax_Syntax.Delta_unfoldable (j)) -> begin
(
# 184 "FStar.TypeChecker.Env.fst"
let k = if (i < j) then begin
i
end else begin
j
end
in FStar_Syntax_Syntax.Delta_unfoldable (k))
end
| (FStar_Syntax_Syntax.Delta_abstract (l1), _58_151) -> begin
(aux l1 l2)
end
| (_58_154, FStar_Syntax_Syntax.Delta_abstract (l2)) -> begin
(aux l1 l2)
end))
in (let _142_390 = (aux l1 l2)
in Unfold (_142_390)))
end))

# 190 "FStar.TypeChecker.Env.fst"
let default_table_size : Prims.int = 200

# 191 "FStar.TypeChecker.Env.fst"
let new_sigtab = (fun _58_158 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))

# 193 "FStar.TypeChecker.Env.fst"
let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t))  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun tc solver module_lid -> (let _142_412 = (FStar_Util.smap_create 100)
in (let _142_411 = (let _142_408 = (new_sigtab ())
in (_142_408)::[])
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _142_412; modules = []; expected_typ = None; sigtab = _142_411; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []; type_of = tc; universe_of = (fun g e -> FStar_Syntax_Syntax.U_zero); use_bv_sorts = false})))

# 219 "FStar.TypeChecker.Env.fst"
let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> (FStar_List.hd env.sigtab))

# 220 "FStar.TypeChecker.Env.fst"
let push : env  ->  Prims.string  ->  env = (fun env msg -> (
# 221 "FStar.TypeChecker.Env.fst"
let _58_167 = (env.solver.push msg)
in (
# 222 "FStar.TypeChecker.Env.fst"
let _58_169 = env
in (let _142_421 = (let _142_420 = (let _142_419 = (sigtab env)
in (FStar_Util.smap_copy _142_419))
in (_142_420)::env.sigtab)
in {solver = _58_169.solver; range = _58_169.range; curmodule = _58_169.curmodule; gamma = _58_169.gamma; gamma_cache = _58_169.gamma_cache; modules = _58_169.modules; expected_typ = _58_169.expected_typ; sigtab = _142_421; is_pattern = _58_169.is_pattern; instantiate_imp = _58_169.instantiate_imp; effects = _58_169.effects; generalize = _58_169.generalize; letrecs = _58_169.letrecs; top_level = _58_169.top_level; check_uvars = _58_169.check_uvars; use_eq = _58_169.use_eq; is_iface = _58_169.is_iface; admit = _58_169.admit; default_effects = _58_169.default_effects; type_of = _58_169.type_of; universe_of = _58_169.universe_of; use_bv_sorts = _58_169.use_bv_sorts}))))

# 223 "FStar.TypeChecker.Env.fst"
let mark : env  ->  env = (fun env -> (
# 224 "FStar.TypeChecker.Env.fst"
let _58_172 = (env.solver.mark "USER MARK")
in (
# 225 "FStar.TypeChecker.Env.fst"
let _58_174 = env
in (let _142_426 = (let _142_425 = (let _142_424 = (sigtab env)
in (FStar_Util.smap_copy _142_424))
in (_142_425)::env.sigtab)
in {solver = _58_174.solver; range = _58_174.range; curmodule = _58_174.curmodule; gamma = _58_174.gamma; gamma_cache = _58_174.gamma_cache; modules = _58_174.modules; expected_typ = _58_174.expected_typ; sigtab = _142_426; is_pattern = _58_174.is_pattern; instantiate_imp = _58_174.instantiate_imp; effects = _58_174.effects; generalize = _58_174.generalize; letrecs = _58_174.letrecs; top_level = _58_174.top_level; check_uvars = _58_174.check_uvars; use_eq = _58_174.use_eq; is_iface = _58_174.is_iface; admit = _58_174.admit; default_effects = _58_174.default_effects; type_of = _58_174.type_of; universe_of = _58_174.universe_of; use_bv_sorts = _58_174.use_bv_sorts}))))

# 226 "FStar.TypeChecker.Env.fst"
let commit_mark : env  ->  env = (fun env -> (
# 227 "FStar.TypeChecker.Env.fst"
let _58_177 = (env.solver.commit_mark "USER MARK")
in (
# 228 "FStar.TypeChecker.Env.fst"
let sigtab = (match (env.sigtab) with
| hd::_58_181::tl -> begin
(hd)::tl
end
| _58_186 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 231 "FStar.TypeChecker.Env.fst"
let _58_188 = env
in {solver = _58_188.solver; range = _58_188.range; curmodule = _58_188.curmodule; gamma = _58_188.gamma; gamma_cache = _58_188.gamma_cache; modules = _58_188.modules; expected_typ = _58_188.expected_typ; sigtab = sigtab; is_pattern = _58_188.is_pattern; instantiate_imp = _58_188.instantiate_imp; effects = _58_188.effects; generalize = _58_188.generalize; letrecs = _58_188.letrecs; top_level = _58_188.top_level; check_uvars = _58_188.check_uvars; use_eq = _58_188.use_eq; is_iface = _58_188.is_iface; admit = _58_188.admit; default_effects = _58_188.default_effects; type_of = _58_188.type_of; universe_of = _58_188.universe_of; use_bv_sorts = _58_188.use_bv_sorts}))))

# 232 "FStar.TypeChecker.Env.fst"
let reset_mark : env  ->  env = (fun env -> (
# 233 "FStar.TypeChecker.Env.fst"
let _58_191 = (env.solver.reset_mark "USER MARK")
in (
# 234 "FStar.TypeChecker.Env.fst"
let _58_193 = env
in (let _142_431 = (FStar_List.tl env.sigtab)
in {solver = _58_193.solver; range = _58_193.range; curmodule = _58_193.curmodule; gamma = _58_193.gamma; gamma_cache = _58_193.gamma_cache; modules = _58_193.modules; expected_typ = _58_193.expected_typ; sigtab = _142_431; is_pattern = _58_193.is_pattern; instantiate_imp = _58_193.instantiate_imp; effects = _58_193.effects; generalize = _58_193.generalize; letrecs = _58_193.letrecs; top_level = _58_193.top_level; check_uvars = _58_193.check_uvars; use_eq = _58_193.use_eq; is_iface = _58_193.is_iface; admit = _58_193.admit; default_effects = _58_193.default_effects; type_of = _58_193.type_of; universe_of = _58_193.universe_of; use_bv_sorts = _58_193.use_bv_sorts}))))

# 235 "FStar.TypeChecker.Env.fst"
let pop : env  ->  Prims.string  ->  env = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(FStar_All.failwith "Too many pops")
end
| _58_203::tl -> begin
(
# 239 "FStar.TypeChecker.Env.fst"
let _58_205 = (env.solver.pop msg)
in (
# 240 "FStar.TypeChecker.Env.fst"
let _58_207 = env
in {solver = _58_207.solver; range = _58_207.range; curmodule = _58_207.curmodule; gamma = _58_207.gamma; gamma_cache = _58_207.gamma_cache; modules = _58_207.modules; expected_typ = _58_207.expected_typ; sigtab = tl; is_pattern = _58_207.is_pattern; instantiate_imp = _58_207.instantiate_imp; effects = _58_207.effects; generalize = _58_207.generalize; letrecs = _58_207.letrecs; top_level = _58_207.top_level; check_uvars = _58_207.check_uvars; use_eq = _58_207.use_eq; is_iface = _58_207.is_iface; admit = _58_207.admit; default_effects = _58_207.default_effects; type_of = _58_207.type_of; universe_of = _58_207.universe_of; use_bv_sorts = _58_207.use_bv_sorts}))
end))

# 245 "FStar.TypeChecker.Env.fst"
let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> ((let _142_441 = (FStar_ST.read FStar_Options.debug)
in (FStar_All.pipe_right _142_441 (FStar_Util.for_some (fun x -> ((env.curmodule.FStar_Ident.str = "") || (env.curmodule.FStar_Ident.str = x)))))) && (FStar_Options.debug_level_geq l)))

# 248 "FStar.TypeChecker.Env.fst"
let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(
# 248 "FStar.TypeChecker.Env.fst"
let _58_214 = e
in {solver = _58_214.solver; range = r; curmodule = _58_214.curmodule; gamma = _58_214.gamma; gamma_cache = _58_214.gamma_cache; modules = _58_214.modules; expected_typ = _58_214.expected_typ; sigtab = _58_214.sigtab; is_pattern = _58_214.is_pattern; instantiate_imp = _58_214.instantiate_imp; effects = _58_214.effects; generalize = _58_214.generalize; letrecs = _58_214.letrecs; top_level = _58_214.top_level; check_uvars = _58_214.check_uvars; use_eq = _58_214.use_eq; is_iface = _58_214.is_iface; admit = _58_214.admit; default_effects = _58_214.default_effects; type_of = _58_214.type_of; universe_of = _58_214.universe_of; use_bv_sorts = _58_214.use_bv_sorts})
end)

# 249 "FStar.TypeChecker.Env.fst"
let get_range : env  ->  FStar_Range.range = (fun e -> e.range)

# 254 "FStar.TypeChecker.Env.fst"
let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)

# 255 "FStar.TypeChecker.Env.fst"
let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)

# 256 "FStar.TypeChecker.Env.fst"
let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (
# 256 "FStar.TypeChecker.Env.fst"
let _58_221 = env
in {solver = _58_221.solver; range = _58_221.range; curmodule = lid; gamma = _58_221.gamma; gamma_cache = _58_221.gamma_cache; modules = _58_221.modules; expected_typ = _58_221.expected_typ; sigtab = _58_221.sigtab; is_pattern = _58_221.is_pattern; instantiate_imp = _58_221.instantiate_imp; effects = _58_221.effects; generalize = _58_221.generalize; letrecs = _58_221.letrecs; top_level = _58_221.top_level; check_uvars = _58_221.check_uvars; use_eq = _58_221.use_eq; is_iface = _58_221.is_iface; admit = _58_221.admit; default_effects = _58_221.default_effects; type_of = _58_221.type_of; universe_of = _58_221.universe_of; use_bv_sorts = _58_221.use_bv_sorts}))

# 257 "FStar.TypeChecker.Env.fst"
let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))

# 258 "FStar.TypeChecker.Env.fst"
let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (let _142_465 = (sigtab env)
in (FStar_Util.smap_try_find _142_465 (FStar_Ident.text_of_lid lid))))

# 260 "FStar.TypeChecker.Env.fst"
let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))

# 263 "FStar.TypeChecker.Env.fst"
let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _142_470 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _142_470)))

# 267 "FStar.TypeChecker.Env.fst"
let new_u_univ = (fun _58_230 -> (let _142_472 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_142_472)))

# 270 "FStar.TypeChecker.Env.fst"
let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match ((ts, us)) with
| (([], t), []) -> begin
([], t)
end
| ((formals, t), _58_243) -> begin
(
# 274 "FStar.TypeChecker.Env.fst"
let _58_245 = ()
in (
# 275 "FStar.TypeChecker.Env.fst"
let n = ((FStar_List.length formals) - 1)
in (
# 276 "FStar.TypeChecker.Env.fst"
let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN (((n - i), u)))))
in (let _142_479 = (FStar_Syntax_Subst.subst vs t)
in (us, _142_479)))))
end))

# 280 "FStar.TypeChecker.Env.fst"
let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _58_1 -> (match (_58_1) with
| ([], t) -> begin
([], t)
end
| (us, t) -> begin
(
# 283 "FStar.TypeChecker.Env.fst"
let us' = (FStar_All.pipe_right us (FStar_List.map (fun _58_258 -> (new_u_univ ()))))
in (inst_tscheme_with (us, t) us'))
end))

# 286 "FStar.TypeChecker.Env.fst"
let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed _58_266 -> (match (_58_266) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(
# 289 "FStar.TypeChecker.Env.fst"
let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in (
# 290 "FStar.TypeChecker.Env.fst"
let _58_269 = if ((FStar_List.length insts) <> (FStar_List.length univs)) then begin
(let _142_495 = (let _142_494 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _142_493 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _142_492 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _142_491 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _142_494 _142_493 _142_492 _142_491)))))
in (FStar_All.failwith _142_495))
end else begin
()
end
in (let _142_496 = (inst_tscheme_with ((FStar_List.append ed.FStar_Syntax_Syntax.univs us), t) insts)
in (Prims.snd _142_496))))
end
| _58_272 -> begin
(let _142_498 = (let _142_497 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _142_497))
in (FStar_All.failwith _142_498))
end)
end))

# 297 "FStar.TypeChecker.Env.fst"
type tri =
| Yes
| No
| Maybe

# 298 "FStar.TypeChecker.Env.fst"
let is_Yes = (fun _discr_ -> (match (_discr_) with
| Yes (_) -> begin
true
end
| _ -> begin
false
end))

# 299 "FStar.TypeChecker.Env.fst"
let is_No = (fun _discr_ -> (match (_discr_) with
| No (_) -> begin
true
end
| _ -> begin
false
end))

# 300 "FStar.TypeChecker.Env.fst"
let is_Maybe = (fun _discr_ -> (match (_discr_) with
| Maybe (_) -> begin
true
end
| _ -> begin
false
end))

# 302 "FStar.TypeChecker.Env.fst"
let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (
# 303 "FStar.TypeChecker.Env.fst"
let cur = (current_module env)
in if (l.FStar_Ident.nsstr = cur.FStar_Ident.str) then begin
Yes
end else begin
if (FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str) then begin
(
# 306 "FStar.TypeChecker.Env.fst"
let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (
# 307 "FStar.TypeChecker.Env.fst"
let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (
# 308 "FStar.TypeChecker.Env.fst"
let rec aux = (fun c l -> (match ((c, l)) with
| ([], _58_283) -> begin
Maybe
end
| (_58_286, []) -> begin
No
end
| (hd::tl, hd'::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _58_297 -> begin
No
end))
in (aux cur lns))))
end else begin
No
end
end))

# 316 "FStar.TypeChecker.Env.fst"
let lookup_qname : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either Prims.option = (fun env lid -> (
# 317 "FStar.TypeChecker.Env.fst"
let cur_mod = (in_cur_mod env lid)
in (
# 318 "FStar.TypeChecker.Env.fst"
let cache = (fun t -> (
# 318 "FStar.TypeChecker.Env.fst"
let _58_303 = (FStar_Util.smap_add env.gamma_cache lid.FStar_Ident.str t)
in Some (t)))
in (
# 319 "FStar.TypeChecker.Env.fst"
let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find env.gamma_cache lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _58_2 -> (match (_58_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _142_518 = (let _142_517 = (inst_tscheme t)
in FStar_Util.Inl (_142_517))
in Some (_142_518))
end else begin
None
end
end
| Binding_sig (_58_312, FStar_Syntax_Syntax.Sig_bundle (ses, _58_315, _58_317, _58_319)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _142_520 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _142_520 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr ((se, None))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(
# 330 "FStar.TypeChecker.Env.fst"
let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_58_332) -> begin
Some (t)
end
| _58_335 -> begin
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
| _58_342 -> begin
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

# 347 "FStar.TypeChecker.Env.fst"
let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| None -> begin
false
end
| Some (_58_352) -> begin
true
end))

# 351 "FStar.TypeChecker.Env.fst"
let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _58_358, _58_360, _58_362) -> begin
(add_sigelts env ses)
end
| _58_366 -> begin
(
# 354 "FStar.TypeChecker.Env.fst"
let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _142_534 = (sigtab env)
in (FStar_Util.smap_add _142_534 l.FStar_Ident.str se))) lids))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))

# 363 "FStar.TypeChecker.Env.fst"
let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun _58_3 -> (match (_58_3) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _58_377 -> begin
None
end))))

# 369 "FStar.TypeChecker.Env.fst"
let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _58_4 -> (match (_58_4) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _58_384 -> begin
false
end)) env.gamma) FStar_Option.isSome))

# 375 "FStar.TypeChecker.Env.fst"
let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_58_388, lb::[]), _58_393, _58_395, _58_397) -> begin
(let _142_554 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_142_554))
end
| FStar_Syntax_Syntax.Sig_let ((_58_401, lbs), _58_405, _58_407, _58_409) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_58_414) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _142_556 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_142_556))
end else begin
None
end
end)))
end
| _58_419 -> begin
None
end))

# 389 "FStar.TypeChecker.Env.fst"
let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _142_564 = (let _142_563 = (let _142_562 = (variable_not_found bv)
in (let _142_561 = (FStar_Syntax_Syntax.range_of_bv bv)
in (_142_562, _142_561)))
in FStar_Syntax_Syntax.Error (_142_563))
in (Prims.raise _142_564))
end
| Some (t) -> begin
t
end))

# 394 "FStar.TypeChecker.Env.fst"
let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _58_428) -> begin
(let _142_570 = (let _142_569 = (let _142_568 = (let _142_567 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _142_567))
in (ne.FStar_Syntax_Syntax.univs, _142_568))
in (inst_tscheme _142_569))
in Some (_142_570))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _58_435, _58_437, _58_439) -> begin
(let _142_574 = (let _142_573 = (let _142_572 = (let _142_571 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _142_571))
in (us, _142_572))
in (inst_tscheme _142_573))
in Some (_142_574))
end
| _58_443 -> begin
None
end))

# 404 "FStar.TypeChecker.Env.fst"
let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_58_453, t) -> begin
Some (t)
end)
end
| _58_458 -> begin
None
end))

# 413 "FStar.TypeChecker.Env.fst"
let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env lid -> (
# 414 "FStar.TypeChecker.Env.fst"
let mapper = (fun _58_5 -> (match (_58_5) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_58_465, uvs, t, _58_469, _58_471, _58_473, _58_475, _58_477), None) -> begin
(let _142_585 = (inst_tscheme (uvs, t))
in Some (_142_585))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _58_488), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _142_586 = (inst_tscheme (uvs, t))
in Some (_142_586))
end else begin
None
end
end else begin
(let _142_587 = (inst_tscheme (uvs, t))
in Some (_142_587))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _58_499, _58_501, _58_503, _58_505), None) -> begin
(match (tps) with
| [] -> begin
(let _142_589 = (inst_tscheme (uvs, k))
in (FStar_All.pipe_left (fun _142_588 -> Some (_142_588)) _142_589))
end
| _58_513 -> begin
(let _142_594 = (let _142_593 = (let _142_592 = (let _142_591 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _142_591))
in (uvs, _142_592))
in (inst_tscheme _142_593))
in (FStar_All.pipe_left (fun _142_590 -> Some (_142_590)) _142_594))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _58_519, _58_521, _58_523, _58_525), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _142_596 = (inst_tscheme_with (uvs, k) us)
in (FStar_All.pipe_left (fun _142_595 -> Some (_142_595)) _142_596))
end
| _58_534 -> begin
(let _142_601 = (let _142_600 = (let _142_599 = (let _142_598 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _142_598))
in (uvs, _142_599))
in (inst_tscheme_with _142_600 us))
in (FStar_All.pipe_left (fun _142_597 -> Some (_142_597)) _142_601))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_58_538), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _58_543 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _142_602 = (lookup_qname env lid)
in (FStar_Util.bind_opt _142_602 mapper))) with
| Some (us, t) -> begin
Some ((us, (
# 448 "FStar.TypeChecker.Env.fst"
let _58_549 = t
in {FStar_Syntax_Syntax.n = _58_549.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_549.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _58_549.FStar_Syntax_Syntax.vars})))
end
| None -> begin
None
end)))

# 451 "FStar.TypeChecker.Env.fst"
let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (
# 452 "FStar.TypeChecker.Env.fst"
let mapper = (fun _58_6 -> (match (_58_6) with
| FStar_Util.Inl (_58_556) -> begin
Some (false)
end
| FStar_Util.Inr (se, _58_560) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (_58_564, _58_566, _58_568, qs, _58_571) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_575) -> begin
Some (true)
end
| _58_578 -> begin
Some (false)
end)
end))
in (match ((let _142_609 = (lookup_qname env lid)
in (FStar_Util.bind_opt _142_609 mapper))) with
| Some (b) -> begin
b
end
| None -> begin
false
end)))

# 467 "FStar.TypeChecker.Env.fst"
let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _142_616 = (let _142_615 = (let _142_614 = (name_not_found l)
in (_142_614, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_142_615))
in (Prims.raise _142_616))
end
| Some (x) -> begin
x
end))

# 472 "FStar.TypeChecker.Env.fst"
let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_58_591, uvs, t, _58_595, _58_597), None)) -> begin
(inst_tscheme (uvs, t))
end
| _58_605 -> begin
(let _142_623 = (let _142_622 = (let _142_621 = (name_not_found lid)
in (_142_621, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_142_622))
in (Prims.raise _142_623))
end))

# 477 "FStar.TypeChecker.Env.fst"
let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_58_609, uvs, t, _58_613, _58_615, _58_617, _58_619, _58_621), None)) -> begin
(inst_tscheme (uvs, t))
end
| _58_629 -> begin
(let _142_630 = (let _142_629 = (let _142_628 = (name_not_found lid)
in (_142_628, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_142_629))
in (Prims.raise _142_630))
end))

# 482 "FStar.TypeChecker.Env.fst"
let lookup_definition : delta_level  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_58_639, lbs), _58_643, _58_645, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (
# 488 "FStar.TypeChecker.Env.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _142_639 = (let _142_638 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (lb.FStar_Syntax_Syntax.lbunivs, _142_638))
in Some (_142_639))
end else begin
None
end)))
end
| _58_652 -> begin
None
end)
end
| _58_654 -> begin
None
end))

# 496 "FStar.TypeChecker.Env.fst"
let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _142_646 = (let _142_645 = (let _142_644 = (name_not_found ftv)
in (_142_644, (FStar_Ident.range_of_lid ftv)))
in FStar_Syntax_Syntax.Error (_142_645))
in (Prims.raise _142_646))
end
| Some (k) -> begin
k
end))

# 501 "FStar.TypeChecker.Env.fst"
let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (
# 502 "FStar.TypeChecker.Env.fst"
let fail = (fun _58_664 -> (match (()) with
| () -> begin
(let _142_657 = (let _142_656 = (FStar_Util.string_of_int i)
in (let _142_655 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _142_656 _142_655)))
in (FStar_All.failwith _142_657))
end))
in (
# 503 "FStar.TypeChecker.Env.fst"
let _58_668 = (lookup_datacon env lid)
in (match (_58_668) with
| (_58_666, t) -> begin
(match ((let _142_658 = (FStar_Syntax_Subst.compress t)
in _142_658.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _58_671) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(
# 508 "FStar.TypeChecker.Env.fst"
let b = (FStar_List.nth binders i)
in (let _142_659 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _142_659 Prims.fst)))
end
end
| _58_676 -> begin
(fail ())
end)
end))))

# 512 "FStar.TypeChecker.Env.fst"
let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_58_680, uvs, t, q, _58_685), None)) -> begin
Some (((uvs, t), q))
end
| _58_693 -> begin
None
end))

# 517 "FStar.TypeChecker.Env.fst"
let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _58_703), None)) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _58_7 -> (match (_58_7) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _58_713 -> begin
false
end)))) then begin
None
end else begin
(
# 522 "FStar.TypeChecker.Env.fst"
let insts = if (FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid) then begin
(univ)::(FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]
end else begin
(univ)::[]
end
in (match ((binders, univs)) with
| ([], _58_717) -> begin
(FStar_All.failwith "Unexpected effect abbreviation with no arguments")
end
| (_58_720, _58_727::_58_724::_58_722) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(let _142_673 = (let _142_672 = (FStar_Syntax_Print.lid_to_string lid)
in (let _142_671 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _142_672 _142_671)))
in (FStar_All.failwith _142_673))
end
| _58_731 -> begin
(
# 530 "FStar.TypeChecker.Env.fst"
let _58_735 = (let _142_675 = (let _142_674 = (FStar_Syntax_Util.arrow binders c)
in (univs, _142_674))
in (inst_tscheme_with _142_675 insts))
in (match (_58_735) with
| (_58_733, t) -> begin
(match ((let _142_676 = (FStar_Syntax_Subst.compress t)
in _142_676.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some ((binders, c))
end
| _58_741 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end))
end
end
| _58_743 -> begin
None
end))

# 539 "FStar.TypeChecker.Env.fst"
let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_58_747, _58_749, _58_751, _58_753, _58_755, dcs, _58_758, _58_760), _58_764)) -> begin
dcs
end
| _58_769 -> begin
[]
end))

# 544 "FStar.TypeChecker.Env.fst"
let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_58_773, _58_775, _58_777, l, _58_780, _58_782, _58_784, _58_786), _58_790)) -> begin
l
end
| _58_795 -> begin
(let _142_686 = (let _142_685 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _142_685))
in (FStar_All.failwith _142_686))
end))

# 549 "FStar.TypeChecker.Env.fst"
let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_58_799, _58_801, _58_803, _58_805, _58_807, _58_809, _58_811, _58_813), _58_817)) -> begin
true
end
| _58_822 -> begin
false
end))

# 554 "FStar.TypeChecker.Env.fst"
let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_58_826, _58_828, _58_830, _58_832, _58_834, _58_836, tags, _58_839), _58_843)) -> begin
(FStar_Util.for_some (fun _58_8 -> (match (_58_8) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _58_855 -> begin
false
end)) tags)
end
| _58_857 -> begin
false
end))

# 560 "FStar.TypeChecker.Env.fst"
let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_58_861, _58_863, _58_865, quals, _58_868), _58_872)) -> begin
(FStar_Util.for_some (fun _58_9 -> (match (_58_9) with
| FStar_Syntax_Syntax.Projector (_58_878) -> begin
true
end
| _58_881 -> begin
false
end)) quals)
end
| _58_883 -> begin
false
end))

# 566 "FStar.TypeChecker.Env.fst"
let interpreted_symbols : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]

# 583 "FStar.TypeChecker.Env.fst"
let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env head -> (match ((let _142_705 = (FStar_Syntax_Util.un_uinst head)
in _142_705.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _58_889 -> begin
false
end))

# 593 "FStar.TypeChecker.Env.fst"
let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))

# 596 "FStar.TypeChecker.Env.fst"
let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _142_717 = (let _142_716 = (let _142_715 = (name_not_found l)
in (_142_715, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_142_716))
in (Prims.raise _142_717))
end
| Some (md) -> begin
md
end))

# 601 "FStar.TypeChecker.Env.fst"
let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
(l1, (fun t wp -> wp), (fun t wp -> wp))
end else begin
if (((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid))) then begin
(FStar_Syntax_Const.effect_GTot_lid, (fun t wp -> wp), (fun t wp -> wp))
end else begin
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _58_917 -> (match (_58_917) with
| (m1, m2, _58_912, _58_914, _58_916) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _142_793 = (let _142_792 = (let _142_791 = (let _142_790 = (FStar_Syntax_Print.lid_to_string l1)
in (let _142_789 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _142_790 _142_789)))
in (_142_791, env.range))
in FStar_Syntax_Syntax.Error (_142_792))
in (Prims.raise _142_793))
end
| Some (_58_920, _58_922, m3, j1, j2) -> begin
(m3, j1, j2)
end)
end
end)

# 611 "FStar.TypeChecker.Env.fst"
let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge Prims.option = (fun env l1 l2 -> if ((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid))) then begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end else begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end)

# 617 "FStar.TypeChecker.Env.fst"
let wp_sig_aux : FStar_Syntax_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun decls m -> (match ((FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))))) with
| None -> begin
(let _142_808 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _142_808))
end
| Some (md) -> begin
(
# 621 "FStar.TypeChecker.Env.fst"
let _58_943 = (inst_tscheme (md.FStar_Syntax_Syntax.univs, md.FStar_Syntax_Syntax.signature))
in (match (_58_943) with
| (_58_941, s) -> begin
(
# 622 "FStar.TypeChecker.Env.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match ((md.FStar_Syntax_Syntax.binders, s.FStar_Syntax_Syntax.n)) with
| ([], FStar_Syntax_Syntax.Tm_arrow ((a, _58_956)::(wp, _58_952)::(wlp, _58_948)::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _58_964 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))

# 627 "FStar.TypeChecker.Env.fst"
let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))

# 629 "FStar.TypeChecker.Env.fst"
let default_effect : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (FStar_Util.find_map env.default_effects (fun _58_971 -> (match (_58_971) with
| (l', m) -> begin
if (FStar_Ident.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))

# 631 "FStar.TypeChecker.Env.fst"
let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, _58_976, _58_978, c, quals, r) -> begin
(match ((FStar_Util.find_map quals (fun _58_10 -> (match (_58_10) with
| FStar_Syntax_Syntax.DefaultEffect (n) -> begin
n
end
| _58_988 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(
# 635 "FStar.TypeChecker.Env.fst"
let _58_992 = env
in {solver = _58_992.solver; range = _58_992.range; curmodule = _58_992.curmodule; gamma = _58_992.gamma; gamma_cache = _58_992.gamma_cache; modules = _58_992.modules; expected_typ = _58_992.expected_typ; sigtab = _58_992.sigtab; is_pattern = _58_992.is_pattern; instantiate_imp = _58_992.instantiate_imp; effects = _58_992.effects; generalize = _58_992.generalize; letrecs = _58_992.letrecs; top_level = _58_992.top_level; check_uvars = _58_992.check_uvars; use_eq = _58_992.use_eq; is_iface = _58_992.is_iface; admit = _58_992.admit; default_effects = ((e, l))::env.default_effects; type_of = _58_992.type_of; universe_of = _58_992.universe_of; use_bv_sorts = _58_992.use_bv_sorts})
end)
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _58_996) -> begin
(
# 638 "FStar.TypeChecker.Env.fst"
let effects = (
# 638 "FStar.TypeChecker.Env.fst"
let _58_999 = env.effects
in {decls = (ne)::env.effects.decls; order = _58_999.order; joins = _58_999.joins})
in (
# 639 "FStar.TypeChecker.Env.fst"
let _58_1002 = env
in {solver = _58_1002.solver; range = _58_1002.range; curmodule = _58_1002.curmodule; gamma = _58_1002.gamma; gamma_cache = _58_1002.gamma_cache; modules = _58_1002.modules; expected_typ = _58_1002.expected_typ; sigtab = _58_1002.sigtab; is_pattern = _58_1002.is_pattern; instantiate_imp = _58_1002.instantiate_imp; effects = effects; generalize = _58_1002.generalize; letrecs = _58_1002.letrecs; top_level = _58_1002.top_level; check_uvars = _58_1002.check_uvars; use_eq = _58_1002.use_eq; is_iface = _58_1002.is_iface; admit = _58_1002.admit; default_effects = _58_1002.default_effects; type_of = _58_1002.type_of; universe_of = _58_1002.universe_of; use_bv_sorts = _58_1002.use_bv_sorts}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _58_1006) -> begin
(
# 642 "FStar.TypeChecker.Env.fst"
let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _142_829 = (e1.mlift r wp1)
in (e2.mlift r _142_829)))})
in (
# 647 "FStar.TypeChecker.Env.fst"
let mk_lift = (fun lift_t r wp1 -> (
# 648 "FStar.TypeChecker.Env.fst"
let _58_1021 = (inst_tscheme lift_t)
in (match (_58_1021) with
| (_58_1019, lift_t) -> begin
(let _142_841 = (let _142_840 = (let _142_839 = (let _142_838 = (FStar_Syntax_Syntax.as_arg r)
in (let _142_837 = (let _142_836 = (FStar_Syntax_Syntax.as_arg wp1)
in (_142_836)::[])
in (_142_838)::_142_837))
in (lift_t, _142_839))
in FStar_Syntax_Syntax.Tm_app (_142_840))
in (FStar_Syntax_Syntax.mk _142_841 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (
# 651 "FStar.TypeChecker.Env.fst"
let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub.FStar_Syntax_Syntax.lift)}
in (
# 655 "FStar.TypeChecker.Env.fst"
let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (
# 660 "FStar.TypeChecker.Env.fst"
let print_mlift = (fun l -> (
# 661 "FStar.TypeChecker.Env.fst"
let arg = (let _142_858 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _142_858 FStar_Syntax_Syntax.Delta_constant None))
in (
# 662 "FStar.TypeChecker.Env.fst"
let wp = (let _142_859 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _142_859 FStar_Syntax_Syntax.Delta_constant None))
in (let _142_860 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _142_860)))))
in (
# 664 "FStar.TypeChecker.Env.fst"
let order = (edge)::env.effects.order
in (
# 666 "FStar.TypeChecker.Env.fst"
let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (
# 668 "FStar.TypeChecker.Env.fst"
let find_edge = (fun order _58_1038 -> (match (_58_1038) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _142_866 -> Some (_142_866)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (
# 677 "FStar.TypeChecker.Env.fst"
let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _142_874 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _142_873 = (find_edge order (i, k))
in (let _142_872 = (find_edge order (k, j))
in (_142_873, _142_872)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _58_1050 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _142_874))) order))
in (
# 688 "FStar.TypeChecker.Env.fst"
let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (
# 690 "FStar.TypeChecker.Env.fst"
let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (
# 693 "FStar.TypeChecker.Env.fst"
let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _142_966 = (find_edge order (i, k))
in (let _142_965 = (find_edge order (j, k))
in (_142_966, _142_965)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _58_1067, _58_1069) -> begin
if ((let _142_967 = (find_edge order (k, ub))
in (FStar_Util.is_some _142_967)) && (not ((let _142_968 = (find_edge order (ub, k))
in (FStar_Util.is_some _142_968))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _58_1073 -> begin
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
# 710 "FStar.TypeChecker.Env.fst"
let effects = (
# 710 "FStar.TypeChecker.Env.fst"
let _58_1082 = env.effects
in {decls = _58_1082.decls; order = order; joins = joins})
in (
# 713 "FStar.TypeChecker.Env.fst"
let _58_1085 = env
in {solver = _58_1085.solver; range = _58_1085.range; curmodule = _58_1085.curmodule; gamma = _58_1085.gamma; gamma_cache = _58_1085.gamma_cache; modules = _58_1085.modules; expected_typ = _58_1085.expected_typ; sigtab = _58_1085.sigtab; is_pattern = _58_1085.is_pattern; instantiate_imp = _58_1085.instantiate_imp; effects = effects; generalize = _58_1085.generalize; letrecs = _58_1085.letrecs; top_level = _58_1085.top_level; check_uvars = _58_1085.check_uvars; use_eq = _58_1085.use_eq; is_iface = _58_1085.is_iface; admit = _58_1085.admit; default_effects = _58_1085.default_effects; type_of = _58_1085.type_of; universe_of = _58_1085.universe_of; use_bv_sorts = _58_1085.use_bv_sorts})))))))))))))
end
| _58_1088 -> begin
env
end))

# 720 "FStar.TypeChecker.Env.fst"
let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (let _142_1017 = (
# 720 "FStar.TypeChecker.Env.fst"
let _58_1091 = env
in (let _142_1016 = (let _142_1015 = (let _142_1014 = (let _142_1013 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_142_1013, s))
in Binding_sig (_142_1014))
in (_142_1015)::env.gamma)
in {solver = _58_1091.solver; range = _58_1091.range; curmodule = _58_1091.curmodule; gamma = _142_1016; gamma_cache = _58_1091.gamma_cache; modules = _58_1091.modules; expected_typ = _58_1091.expected_typ; sigtab = _58_1091.sigtab; is_pattern = _58_1091.is_pattern; instantiate_imp = _58_1091.instantiate_imp; effects = _58_1091.effects; generalize = _58_1091.generalize; letrecs = _58_1091.letrecs; top_level = _58_1091.top_level; check_uvars = _58_1091.check_uvars; use_eq = _58_1091.use_eq; is_iface = _58_1091.is_iface; admit = _58_1091.admit; default_effects = _58_1091.default_effects; type_of = _58_1091.type_of; universe_of = _58_1091.universe_of; use_bv_sorts = _58_1091.use_bv_sorts}))
in (build_lattice _142_1017 s)))

# 722 "FStar.TypeChecker.Env.fst"
let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (let _142_1028 = (
# 722 "FStar.TypeChecker.Env.fst"
let _58_1096 = env
in (let _142_1027 = (let _142_1026 = (let _142_1025 = (let _142_1024 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_142_1024, s, us))
in Binding_sig_inst (_142_1025))
in (_142_1026)::env.gamma)
in {solver = _58_1096.solver; range = _58_1096.range; curmodule = _58_1096.curmodule; gamma = _142_1027; gamma_cache = _58_1096.gamma_cache; modules = _58_1096.modules; expected_typ = _58_1096.expected_typ; sigtab = _58_1096.sigtab; is_pattern = _58_1096.is_pattern; instantiate_imp = _58_1096.instantiate_imp; effects = _58_1096.effects; generalize = _58_1096.generalize; letrecs = _58_1096.letrecs; top_level = _58_1096.top_level; check_uvars = _58_1096.check_uvars; use_eq = _58_1096.use_eq; is_iface = _58_1096.is_iface; admit = _58_1096.admit; default_effects = _58_1096.default_effects; type_of = _58_1096.type_of; universe_of = _58_1096.universe_of; use_bv_sorts = _58_1096.use_bv_sorts}))
in (build_lattice _142_1028 s)))

# 724 "FStar.TypeChecker.Env.fst"
let push_local_binding : env  ->  binding  ->  env = (fun env b -> (
# 724 "FStar.TypeChecker.Env.fst"
let _58_1100 = env
in {solver = _58_1100.solver; range = _58_1100.range; curmodule = _58_1100.curmodule; gamma = (b)::env.gamma; gamma_cache = _58_1100.gamma_cache; modules = _58_1100.modules; expected_typ = _58_1100.expected_typ; sigtab = _58_1100.sigtab; is_pattern = _58_1100.is_pattern; instantiate_imp = _58_1100.instantiate_imp; effects = _58_1100.effects; generalize = _58_1100.generalize; letrecs = _58_1100.letrecs; top_level = _58_1100.top_level; check_uvars = _58_1100.check_uvars; use_eq = _58_1100.use_eq; is_iface = _58_1100.is_iface; admit = _58_1100.admit; default_effects = _58_1100.default_effects; type_of = _58_1100.type_of; universe_of = _58_1100.universe_of; use_bv_sorts = _58_1100.use_bv_sorts}))

# 726 "FStar.TypeChecker.Env.fst"
let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))

# 728 "FStar.TypeChecker.Env.fst"
let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _58_1110 -> (match (_58_1110) with
| (x, _58_1109) -> begin
(push_bv env x)
end)) env bs))

# 731 "FStar.TypeChecker.Env.fst"
let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(
# 733 "FStar.TypeChecker.Env.fst"
let _58_1115 = ()
in (
# 734 "FStar.TypeChecker.Env.fst"
let x = (
# 734 "FStar.TypeChecker.Env.fst"
let _58_1117 = x
in {FStar_Syntax_Syntax.ppname = _58_1117.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1117.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, t))
end))

# 739 "FStar.TypeChecker.Env.fst"
let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))

# 741 "FStar.TypeChecker.Env.fst"
let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (
# 742 "FStar.TypeChecker.Env.fst"
let _58_1127 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (
# 743 "FStar.TypeChecker.Env.fst"
let _58_1129 = env
in {solver = _58_1129.solver; range = _58_1129.range; curmodule = _58_1129.curmodule; gamma = []; gamma_cache = _58_1129.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _58_1129.sigtab; is_pattern = _58_1129.is_pattern; instantiate_imp = _58_1129.instantiate_imp; effects = _58_1129.effects; generalize = _58_1129.generalize; letrecs = _58_1129.letrecs; top_level = _58_1129.top_level; check_uvars = _58_1129.check_uvars; use_eq = _58_1129.use_eq; is_iface = _58_1129.is_iface; admit = _58_1129.admit; default_effects = _58_1129.default_effects; type_of = _58_1129.type_of; universe_of = _58_1129.universe_of; use_bv_sorts = _58_1129.use_bv_sorts})))

# 748 "FStar.TypeChecker.Env.fst"
let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))

# 751 "FStar.TypeChecker.Env.fst"
let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (
# 752 "FStar.TypeChecker.Env.fst"
let _58_1137 = env
in {solver = _58_1137.solver; range = _58_1137.range; curmodule = _58_1137.curmodule; gamma = _58_1137.gamma; gamma_cache = _58_1137.gamma_cache; modules = _58_1137.modules; expected_typ = Some (t); sigtab = _58_1137.sigtab; is_pattern = _58_1137.is_pattern; instantiate_imp = _58_1137.instantiate_imp; effects = _58_1137.effects; generalize = _58_1137.generalize; letrecs = _58_1137.letrecs; top_level = _58_1137.top_level; check_uvars = _58_1137.check_uvars; use_eq = false; is_iface = _58_1137.is_iface; admit = _58_1137.admit; default_effects = _58_1137.default_effects; type_of = _58_1137.type_of; universe_of = _58_1137.universe_of; use_bv_sorts = _58_1137.use_bv_sorts}))

# 754 "FStar.TypeChecker.Env.fst"
let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

# 758 "FStar.TypeChecker.Env.fst"
let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _142_1071 = (expected_typ env)
in ((
# 759 "FStar.TypeChecker.Env.fst"
let _58_1144 = env
in {solver = _58_1144.solver; range = _58_1144.range; curmodule = _58_1144.curmodule; gamma = _58_1144.gamma; gamma_cache = _58_1144.gamma_cache; modules = _58_1144.modules; expected_typ = None; sigtab = _58_1144.sigtab; is_pattern = _58_1144.is_pattern; instantiate_imp = _58_1144.instantiate_imp; effects = _58_1144.effects; generalize = _58_1144.generalize; letrecs = _58_1144.letrecs; top_level = _58_1144.top_level; check_uvars = _58_1144.check_uvars; use_eq = false; is_iface = _58_1144.is_iface; admit = _58_1144.admit; default_effects = _58_1144.default_effects; type_of = _58_1144.type_of; universe_of = _58_1144.universe_of; use_bv_sorts = _58_1144.use_bv_sorts}), _142_1071)))

# 761 "FStar.TypeChecker.Env.fst"
let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (
# 762 "FStar.TypeChecker.Env.fst"
let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (
# 764 "FStar.TypeChecker.Env.fst"
let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(let _142_1077 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _58_11 -> (match (_58_11) with
| Binding_sig (_58_1151, se) -> begin
(se)::[]
end
| _58_1156 -> begin
[]
end))))
in (FStar_All.pipe_right _142_1077 FStar_List.rev))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (
# 770 "FStar.TypeChecker.Env.fst"
let _58_1158 = (add_sigelts env sigs)
in (
# 771 "FStar.TypeChecker.Env.fst"
let _58_1160 = (FStar_Util.smap_clear env.gamma_cache)
in (
# 772 "FStar.TypeChecker.Env.fst"
let _58_1162 = env
in {solver = _58_1162.solver; range = _58_1162.range; curmodule = empty_lid; gamma = []; gamma_cache = _58_1162.gamma_cache; modules = (m)::env.modules; expected_typ = _58_1162.expected_typ; sigtab = _58_1162.sigtab; is_pattern = _58_1162.is_pattern; instantiate_imp = _58_1162.instantiate_imp; effects = _58_1162.effects; generalize = _58_1162.generalize; letrecs = _58_1162.letrecs; top_level = _58_1162.top_level; check_uvars = _58_1162.check_uvars; use_eq = _58_1162.use_eq; is_iface = _58_1162.is_iface; admit = _58_1162.admit; default_effects = _58_1162.default_effects; type_of = _58_1162.type_of; universe_of = _58_1162.universe_of; use_bv_sorts = _58_1162.use_bv_sorts}))))))

# 780 "FStar.TypeChecker.Env.fst"
let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (
# 781 "FStar.TypeChecker.Env.fst"
let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (
# 782 "FStar.TypeChecker.Env.fst"
let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (
# 783 "FStar.TypeChecker.Env.fst"
let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| Binding_univ (_58_1175)::tl -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _142_1089 = (let _142_1088 = (FStar_Syntax_Free.uvars t)
in (ext out _142_1088))
in (aux _142_1089 tl))
end
| (Binding_sig (_)::_) | (Binding_sig_inst (_)::_) -> begin
out
end))
in (aux no_uvs env.gamma)))))

# 792 "FStar.TypeChecker.Env.fst"
let univ_vars : env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun env -> (
# 793 "FStar.TypeChecker.Env.fst"
let no_univs = FStar_Syntax_Syntax.no_universe_uvars
in (
# 794 "FStar.TypeChecker.Env.fst"
let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (
# 795 "FStar.TypeChecker.Env.fst"
let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_sig_inst (_)::tl) | (Binding_univ (_)::tl) -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _142_1101 = (let _142_1100 = (FStar_Syntax_Free.univs t)
in (ext out _142_1100))
in (aux _142_1101 tl))
end
| Binding_sig (_58_1245)::_58_1243 -> begin
out
end))
in (aux no_univs env.gamma)))))

# 804 "FStar.TypeChecker.Env.fst"
let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _58_12 -> (match (_58_12) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))

# 812 "FStar.TypeChecker.Env.fst"
let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _142_1108 = (let _142_1107 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _142_1107 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _142_1108 FStar_List.rev)))

# 814 "FStar.TypeChecker.Env.fst"
let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))

# 816 "FStar.TypeChecker.Env.fst"
let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))

# 818 "FStar.TypeChecker.Env.fst"
let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))

# 820 "FStar.TypeChecker.Env.fst"
let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (
# 821 "FStar.TypeChecker.Env.fst"
let keys = (FStar_List.fold_left (fun keys _58_13 -> (match (_58_13) with
| Binding_sig (lids, _58_1277) -> begin
(FStar_List.append lids keys)
end
| _58_1281 -> begin
keys
end)) [] env.gamma)
in (let _142_1132 = (sigtab env)
in (FStar_Util.smap_fold _142_1132 (fun _58_1283 v keys -> (let _142_1131 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _142_1131 keys))) keys))))

# 828 "FStar.TypeChecker.Env.fst"
let dummy_solver : solver_t = {init = (fun _58_1287 -> ()); push = (fun _58_1289 -> ()); pop = (fun _58_1291 -> ()); mark = (fun _58_1293 -> ()); reset_mark = (fun _58_1295 -> ()); commit_mark = (fun _58_1297 -> ()); encode_modul = (fun _58_1299 _58_1301 -> ()); encode_sig = (fun _58_1303 _58_1305 -> ()); solve = (fun _58_1307 _58_1309 _58_1311 -> ()); is_trivial = (fun _58_1313 _58_1315 -> false); finish = (fun _58_1317 -> ()); refresh = (fun _58_1318 -> ())}

# 843 "FStar.TypeChecker.Env.fst"
let no_solver_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t))  ->  env = (fun tc -> (let _142_1168 = (FStar_Ident.lid_of_path (("dummy")::[]) FStar_Range.dummyRange)
in (initial_env tc dummy_solver _142_1168)))




