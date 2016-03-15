
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
| Binding_var (_58_15) -> begin
_58_15
end))

# 32 "FStar.TypeChecker.Env.fst"
let ___Binding_lid____0 = (fun projectee -> (match (projectee) with
| Binding_lid (_58_18) -> begin
_58_18
end))

# 33 "FStar.TypeChecker.Env.fst"
let ___Binding_sig____0 = (fun projectee -> (match (projectee) with
| Binding_sig (_58_21) -> begin
_58_21
end))

# 34 "FStar.TypeChecker.Env.fst"
let ___Binding_univ____0 = (fun projectee -> (match (projectee) with
| Binding_univ (_58_24) -> begin
_58_24
end))

# 35 "FStar.TypeChecker.Env.fst"
let ___Binding_sig_inst____0 = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_58_27) -> begin
_58_27
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
| Unfold (_58_30) -> begin
_58_30
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

# 164 "FStar.TypeChecker.Env.fst"
let visible_at : delta_level  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun d q -> (match ((d, q)) with
| ((NoDelta, _)) | ((OnlyInline, FStar_Syntax_Syntax.Inline)) | ((Unfold (_), FStar_Syntax_Syntax.Inline)) | ((Unfold (_), FStar_Syntax_Syntax.Unfoldable)) -> begin
true
end
| _58_101 -> begin
false
end))

# 171 "FStar.TypeChecker.Env.fst"
let glb_delta : delta_level  ->  delta_level  ->  delta_level = (fun d1 d2 -> (match ((d1, d2)) with
| ((NoDelta, _)) | ((_, NoDelta)) -> begin
NoDelta
end
| ((OnlyInline, _)) | ((_, OnlyInline)) -> begin
OnlyInline
end
| (Unfold (l1), Unfold (l2)) -> begin
(
# 177 "FStar.TypeChecker.Env.fst"
let rec aux = (fun l1 l2 -> (match ((l1, l2)) with
| ((FStar_Syntax_Syntax.Delta_constant, _)) | ((_, FStar_Syntax_Syntax.Delta_constant)) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| ((FStar_Syntax_Syntax.Delta_equational, l)) | ((l, FStar_Syntax_Syntax.Delta_equational)) -> begin
l
end
| (FStar_Syntax_Syntax.Delta_unfoldable (i), FStar_Syntax_Syntax.Delta_unfoldable (j)) -> begin
(
# 183 "FStar.TypeChecker.Env.fst"
let k = if (i < j) then begin
i
end else begin
j
end
in FStar_Syntax_Syntax.Delta_unfoldable (k))
end
| (FStar_Syntax_Syntax.Delta_abstract (l1), _58_150) -> begin
(aux l1 l2)
end
| (_58_153, FStar_Syntax_Syntax.Delta_abstract (l2)) -> begin
(aux l1 l2)
end))
in (let _142_390 = (aux l1 l2)
in Unfold (_142_390)))
end))

# 189 "FStar.TypeChecker.Env.fst"
let default_table_size : Prims.int = 200

# 190 "FStar.TypeChecker.Env.fst"
let new_sigtab = (fun _58_157 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))

# 192 "FStar.TypeChecker.Env.fst"
let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t))  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun tc solver module_lid -> (let _142_412 = (FStar_Util.smap_create 100)
in (let _142_411 = (let _142_408 = (new_sigtab ())
in (_142_408)::[])
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _142_412; modules = []; expected_typ = None; sigtab = _142_411; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []; type_of = tc; universe_of = (fun g e -> FStar_Syntax_Syntax.U_zero); use_bv_sorts = false})))

# 218 "FStar.TypeChecker.Env.fst"
let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> (FStar_List.hd env.sigtab))

# 219 "FStar.TypeChecker.Env.fst"
let push : env  ->  Prims.string  ->  env = (fun env msg -> (
# 220 "FStar.TypeChecker.Env.fst"
let _58_166 = (env.solver.push msg)
in (
# 221 "FStar.TypeChecker.Env.fst"
let _58_168 = env
in (let _142_421 = (let _142_420 = (let _142_419 = (sigtab env)
in (FStar_Util.smap_copy _142_419))
in (_142_420)::env.sigtab)
in {solver = _58_168.solver; range = _58_168.range; curmodule = _58_168.curmodule; gamma = _58_168.gamma; gamma_cache = _58_168.gamma_cache; modules = _58_168.modules; expected_typ = _58_168.expected_typ; sigtab = _142_421; is_pattern = _58_168.is_pattern; instantiate_imp = _58_168.instantiate_imp; effects = _58_168.effects; generalize = _58_168.generalize; letrecs = _58_168.letrecs; top_level = _58_168.top_level; check_uvars = _58_168.check_uvars; use_eq = _58_168.use_eq; is_iface = _58_168.is_iface; admit = _58_168.admit; default_effects = _58_168.default_effects; type_of = _58_168.type_of; universe_of = _58_168.universe_of; use_bv_sorts = _58_168.use_bv_sorts}))))

# 222 "FStar.TypeChecker.Env.fst"
let mark : env  ->  env = (fun env -> (
# 223 "FStar.TypeChecker.Env.fst"
let _58_171 = (env.solver.mark "USER MARK")
in (
# 224 "FStar.TypeChecker.Env.fst"
let _58_173 = env
in (let _142_426 = (let _142_425 = (let _142_424 = (sigtab env)
in (FStar_Util.smap_copy _142_424))
in (_142_425)::env.sigtab)
in {solver = _58_173.solver; range = _58_173.range; curmodule = _58_173.curmodule; gamma = _58_173.gamma; gamma_cache = _58_173.gamma_cache; modules = _58_173.modules; expected_typ = _58_173.expected_typ; sigtab = _142_426; is_pattern = _58_173.is_pattern; instantiate_imp = _58_173.instantiate_imp; effects = _58_173.effects; generalize = _58_173.generalize; letrecs = _58_173.letrecs; top_level = _58_173.top_level; check_uvars = _58_173.check_uvars; use_eq = _58_173.use_eq; is_iface = _58_173.is_iface; admit = _58_173.admit; default_effects = _58_173.default_effects; type_of = _58_173.type_of; universe_of = _58_173.universe_of; use_bv_sorts = _58_173.use_bv_sorts}))))

# 225 "FStar.TypeChecker.Env.fst"
let commit_mark : env  ->  env = (fun env -> (
# 226 "FStar.TypeChecker.Env.fst"
let _58_176 = (env.solver.commit_mark "USER MARK")
in (
# 227 "FStar.TypeChecker.Env.fst"
let sigtab = (match (env.sigtab) with
| hd::_58_180::tl -> begin
(hd)::tl
end
| _58_185 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 230 "FStar.TypeChecker.Env.fst"
let _58_187 = env
in {solver = _58_187.solver; range = _58_187.range; curmodule = _58_187.curmodule; gamma = _58_187.gamma; gamma_cache = _58_187.gamma_cache; modules = _58_187.modules; expected_typ = _58_187.expected_typ; sigtab = sigtab; is_pattern = _58_187.is_pattern; instantiate_imp = _58_187.instantiate_imp; effects = _58_187.effects; generalize = _58_187.generalize; letrecs = _58_187.letrecs; top_level = _58_187.top_level; check_uvars = _58_187.check_uvars; use_eq = _58_187.use_eq; is_iface = _58_187.is_iface; admit = _58_187.admit; default_effects = _58_187.default_effects; type_of = _58_187.type_of; universe_of = _58_187.universe_of; use_bv_sorts = _58_187.use_bv_sorts}))))

# 231 "FStar.TypeChecker.Env.fst"
let reset_mark : env  ->  env = (fun env -> (
# 232 "FStar.TypeChecker.Env.fst"
let _58_190 = (env.solver.reset_mark "USER MARK")
in (
# 233 "FStar.TypeChecker.Env.fst"
let _58_192 = env
in (let _142_431 = (FStar_List.tl env.sigtab)
in {solver = _58_192.solver; range = _58_192.range; curmodule = _58_192.curmodule; gamma = _58_192.gamma; gamma_cache = _58_192.gamma_cache; modules = _58_192.modules; expected_typ = _58_192.expected_typ; sigtab = _142_431; is_pattern = _58_192.is_pattern; instantiate_imp = _58_192.instantiate_imp; effects = _58_192.effects; generalize = _58_192.generalize; letrecs = _58_192.letrecs; top_level = _58_192.top_level; check_uvars = _58_192.check_uvars; use_eq = _58_192.use_eq; is_iface = _58_192.is_iface; admit = _58_192.admit; default_effects = _58_192.default_effects; type_of = _58_192.type_of; universe_of = _58_192.universe_of; use_bv_sorts = _58_192.use_bv_sorts}))))

# 234 "FStar.TypeChecker.Env.fst"
let pop : env  ->  Prims.string  ->  env = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(FStar_All.failwith "Too many pops")
end
| _58_202::tl -> begin
(
# 238 "FStar.TypeChecker.Env.fst"
let _58_204 = (env.solver.pop msg)
in (
# 239 "FStar.TypeChecker.Env.fst"
let _58_206 = env
in {solver = _58_206.solver; range = _58_206.range; curmodule = _58_206.curmodule; gamma = _58_206.gamma; gamma_cache = _58_206.gamma_cache; modules = _58_206.modules; expected_typ = _58_206.expected_typ; sigtab = tl; is_pattern = _58_206.is_pattern; instantiate_imp = _58_206.instantiate_imp; effects = _58_206.effects; generalize = _58_206.generalize; letrecs = _58_206.letrecs; top_level = _58_206.top_level; check_uvars = _58_206.check_uvars; use_eq = _58_206.use_eq; is_iface = _58_206.is_iface; admit = _58_206.admit; default_effects = _58_206.default_effects; type_of = _58_206.type_of; universe_of = _58_206.universe_of; use_bv_sorts = _58_206.use_bv_sorts}))
end))

# 244 "FStar.TypeChecker.Env.fst"
let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> ((let _142_441 = (FStar_ST.read FStar_Options.debug)
in (FStar_All.pipe_right _142_441 (FStar_Util.for_some (fun x -> ((env.curmodule.FStar_Ident.str = "") || (env.curmodule.FStar_Ident.str = x)))))) && (FStar_Options.debug_level_geq l)))

# 247 "FStar.TypeChecker.Env.fst"
let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(
# 247 "FStar.TypeChecker.Env.fst"
let _58_213 = e
in {solver = _58_213.solver; range = r; curmodule = _58_213.curmodule; gamma = _58_213.gamma; gamma_cache = _58_213.gamma_cache; modules = _58_213.modules; expected_typ = _58_213.expected_typ; sigtab = _58_213.sigtab; is_pattern = _58_213.is_pattern; instantiate_imp = _58_213.instantiate_imp; effects = _58_213.effects; generalize = _58_213.generalize; letrecs = _58_213.letrecs; top_level = _58_213.top_level; check_uvars = _58_213.check_uvars; use_eq = _58_213.use_eq; is_iface = _58_213.is_iface; admit = _58_213.admit; default_effects = _58_213.default_effects; type_of = _58_213.type_of; universe_of = _58_213.universe_of; use_bv_sorts = _58_213.use_bv_sorts})
end)

# 248 "FStar.TypeChecker.Env.fst"
let get_range : env  ->  FStar_Range.range = (fun e -> e.range)

# 253 "FStar.TypeChecker.Env.fst"
let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)

# 254 "FStar.TypeChecker.Env.fst"
let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)

# 255 "FStar.TypeChecker.Env.fst"
let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (
# 255 "FStar.TypeChecker.Env.fst"
let _58_220 = env
in {solver = _58_220.solver; range = _58_220.range; curmodule = lid; gamma = _58_220.gamma; gamma_cache = _58_220.gamma_cache; modules = _58_220.modules; expected_typ = _58_220.expected_typ; sigtab = _58_220.sigtab; is_pattern = _58_220.is_pattern; instantiate_imp = _58_220.instantiate_imp; effects = _58_220.effects; generalize = _58_220.generalize; letrecs = _58_220.letrecs; top_level = _58_220.top_level; check_uvars = _58_220.check_uvars; use_eq = _58_220.use_eq; is_iface = _58_220.is_iface; admit = _58_220.admit; default_effects = _58_220.default_effects; type_of = _58_220.type_of; universe_of = _58_220.universe_of; use_bv_sorts = _58_220.use_bv_sorts}))

# 256 "FStar.TypeChecker.Env.fst"
let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))

# 257 "FStar.TypeChecker.Env.fst"
let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (let _142_465 = (sigtab env)
in (FStar_Util.smap_try_find _142_465 (FStar_Ident.text_of_lid lid))))

# 259 "FStar.TypeChecker.Env.fst"
let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))

# 262 "FStar.TypeChecker.Env.fst"
let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _142_470 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _142_470)))

# 266 "FStar.TypeChecker.Env.fst"
let new_u_univ = (fun _58_229 -> (let _142_472 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_142_472)))

# 269 "FStar.TypeChecker.Env.fst"
let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match ((ts, us)) with
| (([], t), []) -> begin
([], t)
end
| ((formals, t), _58_242) -> begin
(
# 273 "FStar.TypeChecker.Env.fst"
let _58_244 = ()
in (
# 274 "FStar.TypeChecker.Env.fst"
let n = ((FStar_List.length formals) - 1)
in (
# 275 "FStar.TypeChecker.Env.fst"
let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN (((n - i), u)))))
in (let _142_479 = (FStar_Syntax_Subst.subst vs t)
in (us, _142_479)))))
end))

# 279 "FStar.TypeChecker.Env.fst"
let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _58_1 -> (match (_58_1) with
| ([], t) -> begin
([], t)
end
| (us, t) -> begin
(
# 282 "FStar.TypeChecker.Env.fst"
let us' = (FStar_All.pipe_right us (FStar_List.map (fun _58_257 -> (new_u_univ ()))))
in (inst_tscheme_with (us, t) us'))
end))

# 285 "FStar.TypeChecker.Env.fst"
let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed _58_265 -> (match (_58_265) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(
# 288 "FStar.TypeChecker.Env.fst"
let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in (
# 289 "FStar.TypeChecker.Env.fst"
let _58_268 = if ((FStar_List.length insts) <> (FStar_List.length univs)) then begin
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
| _58_271 -> begin
(let _142_498 = (let _142_497 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _142_497))
in (FStar_All.failwith _142_498))
end)
end))

# 296 "FStar.TypeChecker.Env.fst"
type tri =
| Yes
| No
| Maybe

# 297 "FStar.TypeChecker.Env.fst"
let is_Yes = (fun _discr_ -> (match (_discr_) with
| Yes (_) -> begin
true
end
| _ -> begin
false
end))

# 298 "FStar.TypeChecker.Env.fst"
let is_No = (fun _discr_ -> (match (_discr_) with
| No (_) -> begin
true
end
| _ -> begin
false
end))

# 299 "FStar.TypeChecker.Env.fst"
let is_Maybe = (fun _discr_ -> (match (_discr_) with
| Maybe (_) -> begin
true
end
| _ -> begin
false
end))

# 301 "FStar.TypeChecker.Env.fst"
let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (
# 302 "FStar.TypeChecker.Env.fst"
let cur = (current_module env)
in if (l.FStar_Ident.nsstr = cur.FStar_Ident.str) then begin
Yes
end else begin
if (FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str) then begin
(
# 305 "FStar.TypeChecker.Env.fst"
let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (
# 306 "FStar.TypeChecker.Env.fst"
let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (
# 307 "FStar.TypeChecker.Env.fst"
let rec aux = (fun c l -> (match ((c, l)) with
| ([], _58_282) -> begin
Maybe
end
| (_58_285, []) -> begin
No
end
| (hd::tl, hd'::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _58_296 -> begin
No
end))
in (aux cur lns))))
end else begin
No
end
end))

# 315 "FStar.TypeChecker.Env.fst"
let lookup_qname : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either Prims.option = (fun env lid -> (
# 316 "FStar.TypeChecker.Env.fst"
let cur_mod = (in_cur_mod env lid)
in (
# 317 "FStar.TypeChecker.Env.fst"
let cache = (fun t -> (
# 317 "FStar.TypeChecker.Env.fst"
let _58_302 = (FStar_Util.smap_add env.gamma_cache lid.FStar_Ident.str t)
in Some (t)))
in (
# 318 "FStar.TypeChecker.Env.fst"
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
| Binding_sig (_58_311, FStar_Syntax_Syntax.Sig_bundle (ses, _58_314, _58_316, _58_318)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _142_520 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _142_520 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr ((se, None))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(
# 329 "FStar.TypeChecker.Env.fst"
let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_58_331) -> begin
Some (t)
end
| _58_334 -> begin
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
| _58_341 -> begin
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

# 346 "FStar.TypeChecker.Env.fst"
let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| None -> begin
false
end
| Some (_58_351) -> begin
true
end))

# 350 "FStar.TypeChecker.Env.fst"
let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _58_357, _58_359, _58_361) -> begin
(add_sigelts env ses)
end
| _58_365 -> begin
(
# 353 "FStar.TypeChecker.Env.fst"
let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _142_534 = (sigtab env)
in (FStar_Util.smap_add _142_534 l.FStar_Ident.str se))) lids))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))

# 362 "FStar.TypeChecker.Env.fst"
let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun _58_3 -> (match (_58_3) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _58_376 -> begin
None
end))))

# 368 "FStar.TypeChecker.Env.fst"
let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _58_4 -> (match (_58_4) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _58_383 -> begin
false
end)) env.gamma) FStar_Option.isSome))

# 374 "FStar.TypeChecker.Env.fst"
let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_58_387, lb::[]), _58_392, _58_394, _58_396) -> begin
(let _142_554 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_142_554))
end
| FStar_Syntax_Syntax.Sig_let ((_58_400, lbs), _58_404, _58_406, _58_408) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_58_413) -> begin
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
| _58_418 -> begin
None
end))

# 388 "FStar.TypeChecker.Env.fst"
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

# 393 "FStar.TypeChecker.Env.fst"
let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _58_427) -> begin
(let _142_570 = (let _142_569 = (let _142_568 = (let _142_567 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _142_567))
in (ne.FStar_Syntax_Syntax.univs, _142_568))
in (inst_tscheme _142_569))
in Some (_142_570))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _58_434, _58_436, _58_438) -> begin
(let _142_574 = (let _142_573 = (let _142_572 = (let _142_571 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _142_571))
in (us, _142_572))
in (inst_tscheme _142_573))
in Some (_142_574))
end
| _58_442 -> begin
None
end))

# 403 "FStar.TypeChecker.Env.fst"
let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_58_452, t) -> begin
Some (t)
end)
end
| _58_457 -> begin
None
end))

# 412 "FStar.TypeChecker.Env.fst"
let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env lid -> (
# 413 "FStar.TypeChecker.Env.fst"
let mapper = (fun _58_5 -> (match (_58_5) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_58_464, uvs, t, _58_468, _58_470, _58_472, _58_474, _58_476), None) -> begin
(let _142_585 = (inst_tscheme (uvs, t))
in Some (_142_585))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _58_487), None) -> begin
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
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _58_498, _58_500, _58_502, _58_504), None) -> begin
(match (tps) with
| [] -> begin
(let _142_589 = (inst_tscheme (uvs, k))
in (FStar_All.pipe_left (fun _142_588 -> Some (_142_588)) _142_589))
end
| _58_512 -> begin
(let _142_594 = (let _142_593 = (let _142_592 = (let _142_591 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _142_591))
in (uvs, _142_592))
in (inst_tscheme _142_593))
in (FStar_All.pipe_left (fun _142_590 -> Some (_142_590)) _142_594))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _58_518, _58_520, _58_522, _58_524), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _142_596 = (inst_tscheme_with (uvs, k) us)
in (FStar_All.pipe_left (fun _142_595 -> Some (_142_595)) _142_596))
end
| _58_533 -> begin
(let _142_601 = (let _142_600 = (let _142_599 = (let _142_598 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _142_598))
in (uvs, _142_599))
in (inst_tscheme_with _142_600 us))
in (FStar_All.pipe_left (fun _142_597 -> Some (_142_597)) _142_601))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_58_537), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _58_542 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _142_602 = (lookup_qname env lid)
in (FStar_Util.bind_opt _142_602 mapper))) with
| Some (us, t) -> begin
Some ((us, (
# 447 "FStar.TypeChecker.Env.fst"
let _58_548 = t
in {FStar_Syntax_Syntax.n = _58_548.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_548.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _58_548.FStar_Syntax_Syntax.vars})))
end
| None -> begin
None
end)))

# 450 "FStar.TypeChecker.Env.fst"
let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _142_609 = (let _142_608 = (let _142_607 = (name_not_found l)
in (_142_607, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_142_608))
in (Prims.raise _142_609))
end
| Some (x) -> begin
x
end))

# 455 "FStar.TypeChecker.Env.fst"
let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_58_559, uvs, t, _58_563, _58_565), None)) -> begin
(inst_tscheme (uvs, t))
end
| _58_573 -> begin
(let _142_616 = (let _142_615 = (let _142_614 = (name_not_found lid)
in (_142_614, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_142_615))
in (Prims.raise _142_616))
end))

# 460 "FStar.TypeChecker.Env.fst"
let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_58_577, uvs, t, _58_581, _58_583, _58_585, _58_587, _58_589), None)) -> begin
(inst_tscheme (uvs, t))
end
| _58_597 -> begin
(let _142_623 = (let _142_622 = (let _142_621 = (name_not_found lid)
in (_142_621, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_142_622))
in (Prims.raise _142_623))
end))

# 465 "FStar.TypeChecker.Env.fst"
let lookup_definition : delta_level  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_58_607, lbs), _58_611, _58_613, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (
# 471 "FStar.TypeChecker.Env.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _142_632 = (let _142_631 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (lb.FStar_Syntax_Syntax.lbunivs, _142_631))
in Some (_142_632))
end else begin
None
end)))
end
| _58_620 -> begin
None
end)
end
| _58_622 -> begin
None
end))

# 479 "FStar.TypeChecker.Env.fst"
let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _142_639 = (let _142_638 = (let _142_637 = (name_not_found ftv)
in (_142_637, (FStar_Ident.range_of_lid ftv)))
in FStar_Syntax_Syntax.Error (_142_638))
in (Prims.raise _142_639))
end
| Some (k) -> begin
k
end))

# 484 "FStar.TypeChecker.Env.fst"
let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (
# 485 "FStar.TypeChecker.Env.fst"
let fail = (fun _58_632 -> (match (()) with
| () -> begin
(let _142_650 = (let _142_649 = (FStar_Util.string_of_int i)
in (let _142_648 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _142_649 _142_648)))
in (FStar_All.failwith _142_650))
end))
in (
# 486 "FStar.TypeChecker.Env.fst"
let _58_636 = (lookup_datacon env lid)
in (match (_58_636) with
| (_58_634, t) -> begin
(match ((let _142_651 = (FStar_Syntax_Subst.compress t)
in _142_651.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _58_639) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(
# 491 "FStar.TypeChecker.Env.fst"
let b = (FStar_List.nth binders i)
in (let _142_652 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _142_652 Prims.fst)))
end
end
| _58_644 -> begin
(fail ())
end)
end))))

# 495 "FStar.TypeChecker.Env.fst"
let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_58_648, uvs, t, q, _58_653), None)) -> begin
Some (((uvs, t), q))
end
| _58_661 -> begin
None
end))

# 500 "FStar.TypeChecker.Env.fst"
let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _58_671), None)) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _58_6 -> (match (_58_6) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _58_681 -> begin
false
end)))) then begin
None
end else begin
(
# 505 "FStar.TypeChecker.Env.fst"
let insts = if (FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid) then begin
(univ)::(FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]
end else begin
(univ)::[]
end
in (match ((binders, univs)) with
| ([], _58_685) -> begin
(FStar_All.failwith "Unexpected effect abbreviation with no arguments")
end
| (_58_688, _58_695::_58_692::_58_690) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(let _142_666 = (let _142_665 = (FStar_Syntax_Print.lid_to_string lid)
in (let _142_664 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _142_665 _142_664)))
in (FStar_All.failwith _142_666))
end
| _58_699 -> begin
(
# 513 "FStar.TypeChecker.Env.fst"
let _58_703 = (let _142_668 = (let _142_667 = (FStar_Syntax_Util.arrow binders c)
in (univs, _142_667))
in (inst_tscheme_with _142_668 insts))
in (match (_58_703) with
| (_58_701, t) -> begin
(match ((let _142_669 = (FStar_Syntax_Subst.compress t)
in _142_669.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some ((binders, c))
end
| _58_709 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end))
end
end
| _58_711 -> begin
None
end))

# 522 "FStar.TypeChecker.Env.fst"
let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_58_715, _58_717, _58_719, _58_721, _58_723, dcs, _58_726, _58_728), _58_732)) -> begin
dcs
end
| _58_737 -> begin
[]
end))

# 527 "FStar.TypeChecker.Env.fst"
let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_58_741, _58_743, _58_745, l, _58_748, _58_750, _58_752, _58_754), _58_758)) -> begin
l
end
| _58_763 -> begin
(let _142_679 = (let _142_678 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _142_678))
in (FStar_All.failwith _142_679))
end))

# 532 "FStar.TypeChecker.Env.fst"
let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_58_767, _58_769, _58_771, _58_773, _58_775, _58_777, _58_779, _58_781), _58_785)) -> begin
true
end
| _58_790 -> begin
false
end))

# 537 "FStar.TypeChecker.Env.fst"
let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_58_794, _58_796, _58_798, _58_800, _58_802, _58_804, tags, _58_807), _58_811)) -> begin
(FStar_Util.for_some (fun _58_7 -> (match (_58_7) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _58_823 -> begin
false
end)) tags)
end
| _58_825 -> begin
false
end))

# 543 "FStar.TypeChecker.Env.fst"
let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_58_829, _58_831, _58_833, quals, _58_836), _58_840)) -> begin
(FStar_Util.for_some (fun _58_8 -> (match (_58_8) with
| FStar_Syntax_Syntax.Projector (_58_846) -> begin
true
end
| _58_849 -> begin
false
end)) quals)
end
| _58_851 -> begin
false
end))

# 549 "FStar.TypeChecker.Env.fst"
let interpreted_symbols : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]

# 566 "FStar.TypeChecker.Env.fst"
let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env head -> (match ((let _142_698 = (FStar_Syntax_Util.un_uinst head)
in _142_698.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _58_857 -> begin
false
end))

# 576 "FStar.TypeChecker.Env.fst"
let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))

# 579 "FStar.TypeChecker.Env.fst"
let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _142_710 = (let _142_709 = (let _142_708 = (name_not_found l)
in (_142_708, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_142_709))
in (Prims.raise _142_710))
end
| Some (md) -> begin
md
end))

# 584 "FStar.TypeChecker.Env.fst"
let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
(l1, (fun t wp -> wp), (fun t wp -> wp))
end else begin
if (((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid))) then begin
(FStar_Syntax_Const.effect_GTot_lid, (fun t wp -> wp), (fun t wp -> wp))
end else begin
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _58_885 -> (match (_58_885) with
| (m1, m2, _58_880, _58_882, _58_884) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _142_786 = (let _142_785 = (let _142_784 = (let _142_783 = (FStar_Syntax_Print.lid_to_string l1)
in (let _142_782 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _142_783 _142_782)))
in (_142_784, env.range))
in FStar_Syntax_Syntax.Error (_142_785))
in (Prims.raise _142_786))
end
| Some (_58_888, _58_890, m3, j1, j2) -> begin
(m3, j1, j2)
end)
end
end)

# 594 "FStar.TypeChecker.Env.fst"
let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge Prims.option = (fun env l1 l2 -> if ((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid))) then begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end else begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end)

# 600 "FStar.TypeChecker.Env.fst"
let wp_sig_aux : FStar_Syntax_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun decls m -> (match ((FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))))) with
| None -> begin
(let _142_801 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _142_801))
end
| Some (md) -> begin
(
# 604 "FStar.TypeChecker.Env.fst"
let _58_911 = (inst_tscheme (md.FStar_Syntax_Syntax.univs, md.FStar_Syntax_Syntax.signature))
in (match (_58_911) with
| (_58_909, s) -> begin
(
# 605 "FStar.TypeChecker.Env.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match ((md.FStar_Syntax_Syntax.binders, s.FStar_Syntax_Syntax.n)) with
| ([], FStar_Syntax_Syntax.Tm_arrow ((a, _58_924)::(wp, _58_920)::(wlp, _58_916)::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _58_932 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))

# 610 "FStar.TypeChecker.Env.fst"
let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))

# 612 "FStar.TypeChecker.Env.fst"
let default_effect : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (FStar_Util.find_map env.default_effects (fun _58_939 -> (match (_58_939) with
| (l', m) -> begin
if (FStar_Ident.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))

# 614 "FStar.TypeChecker.Env.fst"
let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, _58_944, _58_946, c, quals, r) -> begin
(match ((FStar_Util.find_map quals (fun _58_9 -> (match (_58_9) with
| FStar_Syntax_Syntax.DefaultEffect (n) -> begin
n
end
| _58_956 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(
# 618 "FStar.TypeChecker.Env.fst"
let _58_960 = env
in {solver = _58_960.solver; range = _58_960.range; curmodule = _58_960.curmodule; gamma = _58_960.gamma; gamma_cache = _58_960.gamma_cache; modules = _58_960.modules; expected_typ = _58_960.expected_typ; sigtab = _58_960.sigtab; is_pattern = _58_960.is_pattern; instantiate_imp = _58_960.instantiate_imp; effects = _58_960.effects; generalize = _58_960.generalize; letrecs = _58_960.letrecs; top_level = _58_960.top_level; check_uvars = _58_960.check_uvars; use_eq = _58_960.use_eq; is_iface = _58_960.is_iface; admit = _58_960.admit; default_effects = ((e, l))::env.default_effects; type_of = _58_960.type_of; universe_of = _58_960.universe_of; use_bv_sorts = _58_960.use_bv_sorts})
end)
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _58_964) -> begin
(
# 621 "FStar.TypeChecker.Env.fst"
let effects = (
# 621 "FStar.TypeChecker.Env.fst"
let _58_967 = env.effects
in {decls = (ne)::env.effects.decls; order = _58_967.order; joins = _58_967.joins})
in (
# 622 "FStar.TypeChecker.Env.fst"
let _58_970 = env
in {solver = _58_970.solver; range = _58_970.range; curmodule = _58_970.curmodule; gamma = _58_970.gamma; gamma_cache = _58_970.gamma_cache; modules = _58_970.modules; expected_typ = _58_970.expected_typ; sigtab = _58_970.sigtab; is_pattern = _58_970.is_pattern; instantiate_imp = _58_970.instantiate_imp; effects = effects; generalize = _58_970.generalize; letrecs = _58_970.letrecs; top_level = _58_970.top_level; check_uvars = _58_970.check_uvars; use_eq = _58_970.use_eq; is_iface = _58_970.is_iface; admit = _58_970.admit; default_effects = _58_970.default_effects; type_of = _58_970.type_of; universe_of = _58_970.universe_of; use_bv_sorts = _58_970.use_bv_sorts}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _58_974) -> begin
(
# 625 "FStar.TypeChecker.Env.fst"
let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _142_822 = (e1.mlift r wp1)
in (e2.mlift r _142_822)))})
in (
# 630 "FStar.TypeChecker.Env.fst"
let mk_lift = (fun lift_t r wp1 -> (
# 631 "FStar.TypeChecker.Env.fst"
let _58_989 = (inst_tscheme lift_t)
in (match (_58_989) with
| (_58_987, lift_t) -> begin
(let _142_834 = (let _142_833 = (let _142_832 = (let _142_831 = (FStar_Syntax_Syntax.as_arg r)
in (let _142_830 = (let _142_829 = (FStar_Syntax_Syntax.as_arg wp1)
in (_142_829)::[])
in (_142_831)::_142_830))
in (lift_t, _142_832))
in FStar_Syntax_Syntax.Tm_app (_142_833))
in (FStar_Syntax_Syntax.mk _142_834 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (
# 634 "FStar.TypeChecker.Env.fst"
let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub.FStar_Syntax_Syntax.lift)}
in (
# 638 "FStar.TypeChecker.Env.fst"
let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (
# 643 "FStar.TypeChecker.Env.fst"
let print_mlift = (fun l -> (
# 644 "FStar.TypeChecker.Env.fst"
let arg = (let _142_851 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _142_851 FStar_Syntax_Syntax.Delta_constant None))
in (
# 645 "FStar.TypeChecker.Env.fst"
let wp = (let _142_852 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _142_852 FStar_Syntax_Syntax.Delta_constant None))
in (let _142_853 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _142_853)))))
in (
# 647 "FStar.TypeChecker.Env.fst"
let order = (edge)::env.effects.order
in (
# 649 "FStar.TypeChecker.Env.fst"
let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (
# 651 "FStar.TypeChecker.Env.fst"
let find_edge = (fun order _58_1006 -> (match (_58_1006) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _142_859 -> Some (_142_859)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (
# 660 "FStar.TypeChecker.Env.fst"
let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _142_867 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _142_866 = (find_edge order (i, k))
in (let _142_865 = (find_edge order (k, j))
in (_142_866, _142_865)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _58_1018 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _142_867))) order))
in (
# 671 "FStar.TypeChecker.Env.fst"
let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (
# 673 "FStar.TypeChecker.Env.fst"
let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (
# 676 "FStar.TypeChecker.Env.fst"
let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _142_959 = (find_edge order (i, k))
in (let _142_958 = (find_edge order (j, k))
in (_142_959, _142_958)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _58_1035, _58_1037) -> begin
if ((let _142_960 = (find_edge order (k, ub))
in (FStar_Util.is_some _142_960)) && (not ((let _142_961 = (find_edge order (ub, k))
in (FStar_Util.is_some _142_961))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _58_1041 -> begin
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
# 693 "FStar.TypeChecker.Env.fst"
let effects = (
# 693 "FStar.TypeChecker.Env.fst"
let _58_1050 = env.effects
in {decls = _58_1050.decls; order = order; joins = joins})
in (
# 696 "FStar.TypeChecker.Env.fst"
let _58_1053 = env
in {solver = _58_1053.solver; range = _58_1053.range; curmodule = _58_1053.curmodule; gamma = _58_1053.gamma; gamma_cache = _58_1053.gamma_cache; modules = _58_1053.modules; expected_typ = _58_1053.expected_typ; sigtab = _58_1053.sigtab; is_pattern = _58_1053.is_pattern; instantiate_imp = _58_1053.instantiate_imp; effects = effects; generalize = _58_1053.generalize; letrecs = _58_1053.letrecs; top_level = _58_1053.top_level; check_uvars = _58_1053.check_uvars; use_eq = _58_1053.use_eq; is_iface = _58_1053.is_iface; admit = _58_1053.admit; default_effects = _58_1053.default_effects; type_of = _58_1053.type_of; universe_of = _58_1053.universe_of; use_bv_sorts = _58_1053.use_bv_sorts})))))))))))))
end
| _58_1056 -> begin
env
end))

# 703 "FStar.TypeChecker.Env.fst"
let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (let _142_1010 = (
# 703 "FStar.TypeChecker.Env.fst"
let _58_1059 = env
in (let _142_1009 = (let _142_1008 = (let _142_1007 = (let _142_1006 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_142_1006, s))
in Binding_sig (_142_1007))
in (_142_1008)::env.gamma)
in {solver = _58_1059.solver; range = _58_1059.range; curmodule = _58_1059.curmodule; gamma = _142_1009; gamma_cache = _58_1059.gamma_cache; modules = _58_1059.modules; expected_typ = _58_1059.expected_typ; sigtab = _58_1059.sigtab; is_pattern = _58_1059.is_pattern; instantiate_imp = _58_1059.instantiate_imp; effects = _58_1059.effects; generalize = _58_1059.generalize; letrecs = _58_1059.letrecs; top_level = _58_1059.top_level; check_uvars = _58_1059.check_uvars; use_eq = _58_1059.use_eq; is_iface = _58_1059.is_iface; admit = _58_1059.admit; default_effects = _58_1059.default_effects; type_of = _58_1059.type_of; universe_of = _58_1059.universe_of; use_bv_sorts = _58_1059.use_bv_sorts}))
in (build_lattice _142_1010 s)))

# 705 "FStar.TypeChecker.Env.fst"
let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (let _142_1021 = (
# 705 "FStar.TypeChecker.Env.fst"
let _58_1064 = env
in (let _142_1020 = (let _142_1019 = (let _142_1018 = (let _142_1017 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_142_1017, s, us))
in Binding_sig_inst (_142_1018))
in (_142_1019)::env.gamma)
in {solver = _58_1064.solver; range = _58_1064.range; curmodule = _58_1064.curmodule; gamma = _142_1020; gamma_cache = _58_1064.gamma_cache; modules = _58_1064.modules; expected_typ = _58_1064.expected_typ; sigtab = _58_1064.sigtab; is_pattern = _58_1064.is_pattern; instantiate_imp = _58_1064.instantiate_imp; effects = _58_1064.effects; generalize = _58_1064.generalize; letrecs = _58_1064.letrecs; top_level = _58_1064.top_level; check_uvars = _58_1064.check_uvars; use_eq = _58_1064.use_eq; is_iface = _58_1064.is_iface; admit = _58_1064.admit; default_effects = _58_1064.default_effects; type_of = _58_1064.type_of; universe_of = _58_1064.universe_of; use_bv_sorts = _58_1064.use_bv_sorts}))
in (build_lattice _142_1021 s)))

# 707 "FStar.TypeChecker.Env.fst"
let push_local_binding : env  ->  binding  ->  env = (fun env b -> (
# 707 "FStar.TypeChecker.Env.fst"
let _58_1068 = env
in {solver = _58_1068.solver; range = _58_1068.range; curmodule = _58_1068.curmodule; gamma = (b)::env.gamma; gamma_cache = _58_1068.gamma_cache; modules = _58_1068.modules; expected_typ = _58_1068.expected_typ; sigtab = _58_1068.sigtab; is_pattern = _58_1068.is_pattern; instantiate_imp = _58_1068.instantiate_imp; effects = _58_1068.effects; generalize = _58_1068.generalize; letrecs = _58_1068.letrecs; top_level = _58_1068.top_level; check_uvars = _58_1068.check_uvars; use_eq = _58_1068.use_eq; is_iface = _58_1068.is_iface; admit = _58_1068.admit; default_effects = _58_1068.default_effects; type_of = _58_1068.type_of; universe_of = _58_1068.universe_of; use_bv_sorts = _58_1068.use_bv_sorts}))

# 709 "FStar.TypeChecker.Env.fst"
let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))

# 711 "FStar.TypeChecker.Env.fst"
let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _58_1078 -> (match (_58_1078) with
| (x, _58_1077) -> begin
(push_bv env x)
end)) env bs))

# 714 "FStar.TypeChecker.Env.fst"
let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(
# 716 "FStar.TypeChecker.Env.fst"
let _58_1083 = ()
in (
# 717 "FStar.TypeChecker.Env.fst"
let x = (
# 717 "FStar.TypeChecker.Env.fst"
let _58_1085 = x
in {FStar_Syntax_Syntax.ppname = _58_1085.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1085.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, t))
end))

# 722 "FStar.TypeChecker.Env.fst"
let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))

# 724 "FStar.TypeChecker.Env.fst"
let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (
# 725 "FStar.TypeChecker.Env.fst"
let _58_1095 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (
# 726 "FStar.TypeChecker.Env.fst"
let _58_1097 = env
in {solver = _58_1097.solver; range = _58_1097.range; curmodule = _58_1097.curmodule; gamma = []; gamma_cache = _58_1097.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _58_1097.sigtab; is_pattern = _58_1097.is_pattern; instantiate_imp = _58_1097.instantiate_imp; effects = _58_1097.effects; generalize = _58_1097.generalize; letrecs = _58_1097.letrecs; top_level = _58_1097.top_level; check_uvars = _58_1097.check_uvars; use_eq = _58_1097.use_eq; is_iface = _58_1097.is_iface; admit = _58_1097.admit; default_effects = _58_1097.default_effects; type_of = _58_1097.type_of; universe_of = _58_1097.universe_of; use_bv_sorts = _58_1097.use_bv_sorts})))

# 731 "FStar.TypeChecker.Env.fst"
let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))

# 734 "FStar.TypeChecker.Env.fst"
let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (
# 735 "FStar.TypeChecker.Env.fst"
let _58_1105 = env
in {solver = _58_1105.solver; range = _58_1105.range; curmodule = _58_1105.curmodule; gamma = _58_1105.gamma; gamma_cache = _58_1105.gamma_cache; modules = _58_1105.modules; expected_typ = Some (t); sigtab = _58_1105.sigtab; is_pattern = _58_1105.is_pattern; instantiate_imp = _58_1105.instantiate_imp; effects = _58_1105.effects; generalize = _58_1105.generalize; letrecs = _58_1105.letrecs; top_level = _58_1105.top_level; check_uvars = _58_1105.check_uvars; use_eq = false; is_iface = _58_1105.is_iface; admit = _58_1105.admit; default_effects = _58_1105.default_effects; type_of = _58_1105.type_of; universe_of = _58_1105.universe_of; use_bv_sorts = _58_1105.use_bv_sorts}))

# 737 "FStar.TypeChecker.Env.fst"
let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

# 741 "FStar.TypeChecker.Env.fst"
let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _142_1064 = (expected_typ env)
in ((
# 742 "FStar.TypeChecker.Env.fst"
let _58_1112 = env
in {solver = _58_1112.solver; range = _58_1112.range; curmodule = _58_1112.curmodule; gamma = _58_1112.gamma; gamma_cache = _58_1112.gamma_cache; modules = _58_1112.modules; expected_typ = None; sigtab = _58_1112.sigtab; is_pattern = _58_1112.is_pattern; instantiate_imp = _58_1112.instantiate_imp; effects = _58_1112.effects; generalize = _58_1112.generalize; letrecs = _58_1112.letrecs; top_level = _58_1112.top_level; check_uvars = _58_1112.check_uvars; use_eq = false; is_iface = _58_1112.is_iface; admit = _58_1112.admit; default_effects = _58_1112.default_effects; type_of = _58_1112.type_of; universe_of = _58_1112.universe_of; use_bv_sorts = _58_1112.use_bv_sorts}), _142_1064)))

# 744 "FStar.TypeChecker.Env.fst"
let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (
# 745 "FStar.TypeChecker.Env.fst"
let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (
# 747 "FStar.TypeChecker.Env.fst"
let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(FStar_All.pipe_right env.gamma (FStar_List.collect (fun _58_10 -> (match (_58_10) with
| Binding_sig (_58_1119, se) -> begin
(se)::[]
end
| _58_1124 -> begin
[]
end))))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (
# 753 "FStar.TypeChecker.Env.fst"
let _58_1126 = (add_sigelts env sigs)
in (
# 754 "FStar.TypeChecker.Env.fst"
let _58_1128 = (FStar_Util.smap_clear env.gamma_cache)
in (
# 755 "FStar.TypeChecker.Env.fst"
let _58_1130 = env
in {solver = _58_1130.solver; range = _58_1130.range; curmodule = empty_lid; gamma = []; gamma_cache = _58_1130.gamma_cache; modules = (m)::env.modules; expected_typ = _58_1130.expected_typ; sigtab = _58_1130.sigtab; is_pattern = _58_1130.is_pattern; instantiate_imp = _58_1130.instantiate_imp; effects = _58_1130.effects; generalize = _58_1130.generalize; letrecs = _58_1130.letrecs; top_level = _58_1130.top_level; check_uvars = _58_1130.check_uvars; use_eq = _58_1130.use_eq; is_iface = _58_1130.is_iface; admit = _58_1130.admit; default_effects = _58_1130.default_effects; type_of = _58_1130.type_of; universe_of = _58_1130.universe_of; use_bv_sorts = _58_1130.use_bv_sorts}))))))

# 763 "FStar.TypeChecker.Env.fst"
let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (
# 764 "FStar.TypeChecker.Env.fst"
let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (
# 765 "FStar.TypeChecker.Env.fst"
let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (
# 766 "FStar.TypeChecker.Env.fst"
let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| Binding_univ (_58_1143)::tl -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _142_1081 = (let _142_1080 = (FStar_Syntax_Free.uvars t)
in (ext out _142_1080))
in (aux _142_1081 tl))
end
| (Binding_sig (_)::_) | (Binding_sig_inst (_)::_) -> begin
out
end))
in (aux no_uvs env.gamma)))))

# 775 "FStar.TypeChecker.Env.fst"
let univ_vars : env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun env -> (
# 776 "FStar.TypeChecker.Env.fst"
let no_univs = FStar_Syntax_Syntax.no_universe_uvars
in (
# 777 "FStar.TypeChecker.Env.fst"
let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (
# 778 "FStar.TypeChecker.Env.fst"
let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_sig_inst (_)::tl) | (Binding_univ (_)::tl) -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _142_1093 = (let _142_1092 = (FStar_Syntax_Free.univs t)
in (ext out _142_1092))
in (aux _142_1093 tl))
end
| Binding_sig (_58_1213)::_58_1211 -> begin
out
end))
in (aux no_univs env.gamma)))))

# 787 "FStar.TypeChecker.Env.fst"
let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _58_11 -> (match (_58_11) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))

# 795 "FStar.TypeChecker.Env.fst"
let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _142_1100 = (let _142_1099 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _142_1099 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _142_1100 FStar_List.rev)))

# 797 "FStar.TypeChecker.Env.fst"
let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))

# 799 "FStar.TypeChecker.Env.fst"
let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))

# 801 "FStar.TypeChecker.Env.fst"
let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))

# 803 "FStar.TypeChecker.Env.fst"
let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (
# 804 "FStar.TypeChecker.Env.fst"
let keys = (FStar_List.fold_left (fun keys _58_12 -> (match (_58_12) with
| Binding_sig (lids, _58_1245) -> begin
(FStar_List.append lids keys)
end
| _58_1249 -> begin
keys
end)) [] env.gamma)
in (let _142_1124 = (sigtab env)
in (FStar_Util.smap_fold _142_1124 (fun _58_1251 v keys -> (let _142_1123 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _142_1123 keys))) keys))))

# 811 "FStar.TypeChecker.Env.fst"
let dummy_solver : solver_t = {init = (fun _58_1255 -> ()); push = (fun _58_1257 -> ()); pop = (fun _58_1259 -> ()); mark = (fun _58_1261 -> ()); reset_mark = (fun _58_1263 -> ()); commit_mark = (fun _58_1265 -> ()); encode_modul = (fun _58_1267 _58_1269 -> ()); encode_sig = (fun _58_1271 _58_1273 -> ()); solve = (fun _58_1275 _58_1277 _58_1279 -> ()); is_trivial = (fun _58_1281 _58_1283 -> false); finish = (fun _58_1285 -> ()); refresh = (fun _58_1286 -> ())}

# 826 "FStar.TypeChecker.Env.fst"
let no_solver_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t))  ->  env = (fun tc -> (let _142_1160 = (FStar_Ident.lid_of_path (("dummy")::[]) FStar_Range.dummyRange)
in (initial_env tc dummy_solver _142_1160)))




