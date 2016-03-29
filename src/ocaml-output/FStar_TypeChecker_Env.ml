
open Prims
# 28 "FStar.TypeChecker.Env.fst"
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
| Binding_var (_53_16) -> begin
_53_16
end))

# 32 "FStar.TypeChecker.Env.fst"
let ___Binding_lid____0 = (fun projectee -> (match (projectee) with
| Binding_lid (_53_19) -> begin
_53_19
end))

# 33 "FStar.TypeChecker.Env.fst"
let ___Binding_sig____0 = (fun projectee -> (match (projectee) with
| Binding_sig (_53_22) -> begin
_53_22
end))

# 34 "FStar.TypeChecker.Env.fst"
let ___Binding_univ____0 = (fun projectee -> (match (projectee) with
| Binding_univ (_53_25) -> begin
_53_25
end))

# 35 "FStar.TypeChecker.Env.fst"
let ___Binding_sig_inst____0 = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_53_28) -> begin
_53_28
end))

# 35 "FStar.TypeChecker.Env.fst"
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
| Unfold (_53_31) -> begin
_53_31
end))

# 40 "FStar.TypeChecker.Env.fst"
type mlift =
FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ

# 42 "FStar.TypeChecker.Env.fst"
type edge =
{msource : FStar_Ident.lident; mtarget : FStar_Ident.lident; mlift : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ}

# 44 "FStar.TypeChecker.Env.fst"
let is_Mkedge : edge  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkedge"))))

# 48 "FStar.TypeChecker.Env.fst"
type effects =
{decls : FStar_Syntax_Syntax.eff_decl Prims.list; order : edge Prims.list; joins : (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list}

# 49 "FStar.TypeChecker.Env.fst"
let is_Mkeffects : effects  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeffects"))))

# 53 "FStar.TypeChecker.Env.fst"
type cached_elt =
((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either

# 54 "FStar.TypeChecker.Env.fst"
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

# 98 "FStar.TypeChecker.Env.fst"
type env_t =
env

# 99 "FStar.TypeChecker.Env.fst"
type implicits =
(env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list

# 100 "FStar.TypeChecker.Env.fst"
type sigtable =
FStar_Syntax_Syntax.sigelt FStar_Util.smap

# 163 "FStar.TypeChecker.Env.fst"
let visible_at : delta_level  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun d q -> (match ((d, q)) with
| ((NoDelta, _)) | ((OnlyInline, FStar_Syntax_Syntax.Inline)) | ((Unfold (_), FStar_Syntax_Syntax.Inline)) | ((Unfold (_), FStar_Syntax_Syntax.Unfoldable)) -> begin
true
end
| _53_102 -> begin
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
| (FStar_Syntax_Syntax.Delta_abstract (l1), _53_151) -> begin
(aux l1 l2)
end
| (_53_154, FStar_Syntax_Syntax.Delta_abstract (l2)) -> begin
(aux l1 l2)
end))
in (let _132_390 = (aux l1 l2)
in Unfold (_132_390)))
end))

# 188 "FStar.TypeChecker.Env.fst"
let default_table_size : Prims.int = 200

# 190 "FStar.TypeChecker.Env.fst"
let new_sigtab = (fun _53_158 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))

# 191 "FStar.TypeChecker.Env.fst"
let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t))  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun tc solver module_lid -> (let _132_412 = (FStar_Util.smap_create 100)
in (let _132_411 = (let _132_408 = (new_sigtab ())
in (_132_408)::[])
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _132_412; modules = []; expected_typ = None; sigtab = _132_411; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []; type_of = tc; universe_of = (fun g e -> FStar_Syntax_Syntax.U_zero); use_bv_sorts = false})))

# 216 "FStar.TypeChecker.Env.fst"
let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> (FStar_List.hd env.sigtab))

# 219 "FStar.TypeChecker.Env.fst"
let push : env  ->  Prims.string  ->  env = (fun env msg -> (
# 221 "FStar.TypeChecker.Env.fst"
let _53_167 = (env.solver.push msg)
in (
# 222 "FStar.TypeChecker.Env.fst"
let _53_169 = env
in (let _132_421 = (let _132_420 = (let _132_419 = (sigtab env)
in (FStar_Util.smap_copy _132_419))
in (_132_420)::env.sigtab)
in {solver = _53_169.solver; range = _53_169.range; curmodule = _53_169.curmodule; gamma = _53_169.gamma; gamma_cache = _53_169.gamma_cache; modules = _53_169.modules; expected_typ = _53_169.expected_typ; sigtab = _132_421; is_pattern = _53_169.is_pattern; instantiate_imp = _53_169.instantiate_imp; effects = _53_169.effects; generalize = _53_169.generalize; letrecs = _53_169.letrecs; top_level = _53_169.top_level; check_uvars = _53_169.check_uvars; use_eq = _53_169.use_eq; is_iface = _53_169.is_iface; admit = _53_169.admit; default_effects = _53_169.default_effects; type_of = _53_169.type_of; universe_of = _53_169.universe_of; use_bv_sorts = _53_169.use_bv_sorts}))))

# 222 "FStar.TypeChecker.Env.fst"
let mark : env  ->  env = (fun env -> (
# 224 "FStar.TypeChecker.Env.fst"
let _53_172 = (env.solver.mark "USER MARK")
in (
# 225 "FStar.TypeChecker.Env.fst"
let _53_174 = env
in (let _132_426 = (let _132_425 = (let _132_424 = (sigtab env)
in (FStar_Util.smap_copy _132_424))
in (_132_425)::env.sigtab)
in {solver = _53_174.solver; range = _53_174.range; curmodule = _53_174.curmodule; gamma = _53_174.gamma; gamma_cache = _53_174.gamma_cache; modules = _53_174.modules; expected_typ = _53_174.expected_typ; sigtab = _132_426; is_pattern = _53_174.is_pattern; instantiate_imp = _53_174.instantiate_imp; effects = _53_174.effects; generalize = _53_174.generalize; letrecs = _53_174.letrecs; top_level = _53_174.top_level; check_uvars = _53_174.check_uvars; use_eq = _53_174.use_eq; is_iface = _53_174.is_iface; admit = _53_174.admit; default_effects = _53_174.default_effects; type_of = _53_174.type_of; universe_of = _53_174.universe_of; use_bv_sorts = _53_174.use_bv_sorts}))))

# 225 "FStar.TypeChecker.Env.fst"
let commit_mark : env  ->  env = (fun env -> (
# 227 "FStar.TypeChecker.Env.fst"
let _53_177 = (env.solver.commit_mark "USER MARK")
in (
# 228 "FStar.TypeChecker.Env.fst"
let sigtab = (match (env.sigtab) with
| hd::_53_181::tl -> begin
(hd)::tl
end
| _53_186 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 231 "FStar.TypeChecker.Env.fst"
let _53_188 = env
in {solver = _53_188.solver; range = _53_188.range; curmodule = _53_188.curmodule; gamma = _53_188.gamma; gamma_cache = _53_188.gamma_cache; modules = _53_188.modules; expected_typ = _53_188.expected_typ; sigtab = sigtab; is_pattern = _53_188.is_pattern; instantiate_imp = _53_188.instantiate_imp; effects = _53_188.effects; generalize = _53_188.generalize; letrecs = _53_188.letrecs; top_level = _53_188.top_level; check_uvars = _53_188.check_uvars; use_eq = _53_188.use_eq; is_iface = _53_188.is_iface; admit = _53_188.admit; default_effects = _53_188.default_effects; type_of = _53_188.type_of; universe_of = _53_188.universe_of; use_bv_sorts = _53_188.use_bv_sorts}))))

# 231 "FStar.TypeChecker.Env.fst"
let reset_mark : env  ->  env = (fun env -> (
# 233 "FStar.TypeChecker.Env.fst"
let _53_191 = (env.solver.reset_mark "USER MARK")
in (
# 234 "FStar.TypeChecker.Env.fst"
let _53_193 = env
in (let _132_431 = (FStar_List.tl env.sigtab)
in {solver = _53_193.solver; range = _53_193.range; curmodule = _53_193.curmodule; gamma = _53_193.gamma; gamma_cache = _53_193.gamma_cache; modules = _53_193.modules; expected_typ = _53_193.expected_typ; sigtab = _132_431; is_pattern = _53_193.is_pattern; instantiate_imp = _53_193.instantiate_imp; effects = _53_193.effects; generalize = _53_193.generalize; letrecs = _53_193.letrecs; top_level = _53_193.top_level; check_uvars = _53_193.check_uvars; use_eq = _53_193.use_eq; is_iface = _53_193.is_iface; admit = _53_193.admit; default_effects = _53_193.default_effects; type_of = _53_193.type_of; universe_of = _53_193.universe_of; use_bv_sorts = _53_193.use_bv_sorts}))))

# 234 "FStar.TypeChecker.Env.fst"
let pop : env  ->  Prims.string  ->  env = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(FStar_All.failwith "Too many pops")
end
| _53_203::tl -> begin
(
# 239 "FStar.TypeChecker.Env.fst"
let _53_205 = (env.solver.pop msg)
in (
# 240 "FStar.TypeChecker.Env.fst"
let _53_207 = env
in {solver = _53_207.solver; range = _53_207.range; curmodule = _53_207.curmodule; gamma = _53_207.gamma; gamma_cache = _53_207.gamma_cache; modules = _53_207.modules; expected_typ = _53_207.expected_typ; sigtab = tl; is_pattern = _53_207.is_pattern; instantiate_imp = _53_207.instantiate_imp; effects = _53_207.effects; generalize = _53_207.generalize; letrecs = _53_207.letrecs; top_level = _53_207.top_level; check_uvars = _53_207.check_uvars; use_eq = _53_207.use_eq; is_iface = _53_207.is_iface; admit = _53_207.admit; default_effects = _53_207.default_effects; type_of = _53_207.type_of; universe_of = _53_207.universe_of; use_bv_sorts = _53_207.use_bv_sorts}))
end))

# 240 "FStar.TypeChecker.Env.fst"
let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> ((let _132_441 = (FStar_ST.read FStar_Options.debug)
in (FStar_All.pipe_right _132_441 (FStar_Util.for_some (fun x -> ((env.curmodule.FStar_Ident.str = "") || (env.curmodule.FStar_Ident.str = x)))))) && (FStar_Options.debug_level_geq l)))

# 247 "FStar.TypeChecker.Env.fst"
let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(
# 248 "FStar.TypeChecker.Env.fst"
let _53_214 = e
in {solver = _53_214.solver; range = r; curmodule = _53_214.curmodule; gamma = _53_214.gamma; gamma_cache = _53_214.gamma_cache; modules = _53_214.modules; expected_typ = _53_214.expected_typ; sigtab = _53_214.sigtab; is_pattern = _53_214.is_pattern; instantiate_imp = _53_214.instantiate_imp; effects = _53_214.effects; generalize = _53_214.generalize; letrecs = _53_214.letrecs; top_level = _53_214.top_level; check_uvars = _53_214.check_uvars; use_eq = _53_214.use_eq; is_iface = _53_214.is_iface; admit = _53_214.admit; default_effects = _53_214.default_effects; type_of = _53_214.type_of; universe_of = _53_214.universe_of; use_bv_sorts = _53_214.use_bv_sorts})
end)

# 248 "FStar.TypeChecker.Env.fst"
let get_range : env  ->  FStar_Range.range = (fun e -> e.range)

# 249 "FStar.TypeChecker.Env.fst"
let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)

# 254 "FStar.TypeChecker.Env.fst"
let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)

# 255 "FStar.TypeChecker.Env.fst"
let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (
# 256 "FStar.TypeChecker.Env.fst"
let _53_221 = env
in {solver = _53_221.solver; range = _53_221.range; curmodule = lid; gamma = _53_221.gamma; gamma_cache = _53_221.gamma_cache; modules = _53_221.modules; expected_typ = _53_221.expected_typ; sigtab = _53_221.sigtab; is_pattern = _53_221.is_pattern; instantiate_imp = _53_221.instantiate_imp; effects = _53_221.effects; generalize = _53_221.generalize; letrecs = _53_221.letrecs; top_level = _53_221.top_level; check_uvars = _53_221.check_uvars; use_eq = _53_221.use_eq; is_iface = _53_221.is_iface; admit = _53_221.admit; default_effects = _53_221.default_effects; type_of = _53_221.type_of; universe_of = _53_221.universe_of; use_bv_sorts = _53_221.use_bv_sorts}))

# 256 "FStar.TypeChecker.Env.fst"
let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))

# 257 "FStar.TypeChecker.Env.fst"
let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (let _132_465 = (sigtab env)
in (FStar_Util.smap_try_find _132_465 (FStar_Ident.text_of_lid lid))))

# 258 "FStar.TypeChecker.Env.fst"
let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))

# 261 "FStar.TypeChecker.Env.fst"
let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _132_470 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _132_470)))

# 264 "FStar.TypeChecker.Env.fst"
let new_u_univ = (fun _53_230 -> (let _132_472 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_132_472)))

# 267 "FStar.TypeChecker.Env.fst"
let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match ((ts, us)) with
| (([], t), []) -> begin
([], t)
end
| ((formals, t), _53_243) -> begin
(
# 274 "FStar.TypeChecker.Env.fst"
let _53_245 = ()
in (
# 275 "FStar.TypeChecker.Env.fst"
let n = ((FStar_List.length formals) - 1)
in (
# 276 "FStar.TypeChecker.Env.fst"
let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN (((n - i), u)))))
in (let _132_479 = (FStar_Syntax_Subst.subst vs t)
in (us, _132_479)))))
end))

# 277 "FStar.TypeChecker.Env.fst"
let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _53_1 -> (match (_53_1) with
| ([], t) -> begin
([], t)
end
| (us, t) -> begin
(
# 283 "FStar.TypeChecker.Env.fst"
let us' = (FStar_All.pipe_right us (FStar_List.map (fun _53_258 -> (new_u_univ ()))))
in (inst_tscheme_with (us, t) us'))
end))

# 284 "FStar.TypeChecker.Env.fst"
let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed _53_266 -> (match (_53_266) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(
# 289 "FStar.TypeChecker.Env.fst"
let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in (
# 290 "FStar.TypeChecker.Env.fst"
let _53_269 = if ((FStar_List.length insts) <> (FStar_List.length univs)) then begin
(let _132_495 = (let _132_494 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _132_493 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _132_492 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _132_491 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _132_494 _132_493 _132_492 _132_491)))))
in (FStar_All.failwith _132_495))
end else begin
()
end
in (let _132_496 = (inst_tscheme_with ((FStar_List.append ed.FStar_Syntax_Syntax.univs us), t) insts)
in (Prims.snd _132_496))))
end
| _53_272 -> begin
(let _132_498 = (let _132_497 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _132_497))
in (FStar_All.failwith _132_498))
end)
end))

# 295 "FStar.TypeChecker.Env.fst"
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

# 300 "FStar.TypeChecker.Env.fst"
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
| ([], _53_283) -> begin
Maybe
end
| (_53_286, []) -> begin
No
end
| (hd::tl, hd'::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _53_297 -> begin
No
end))
in (aux cur lns))))
end else begin
No
end
end))

# 314 "FStar.TypeChecker.Env.fst"
let lookup_qname : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either Prims.option = (fun env lid -> (
# 317 "FStar.TypeChecker.Env.fst"
let cur_mod = (in_cur_mod env lid)
in (
# 318 "FStar.TypeChecker.Env.fst"
let cache = (fun t -> (
# 318 "FStar.TypeChecker.Env.fst"
let _53_303 = (FStar_Util.smap_add env.gamma_cache lid.FStar_Ident.str t)
in Some (t)))
in (
# 319 "FStar.TypeChecker.Env.fst"
let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find env.gamma_cache lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _53_2 -> (match (_53_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _132_518 = (let _132_517 = (inst_tscheme t)
in FStar_Util.Inl (_132_517))
in Some (_132_518))
end else begin
None
end
end
| Binding_sig (_53_312, FStar_Syntax_Syntax.Sig_bundle (ses, _53_315, _53_317, _53_319)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _132_520 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _132_520 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr ((se, None))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(
# 330 "FStar.TypeChecker.Env.fst"
let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_53_332) -> begin
Some (t)
end
| _53_335 -> begin
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
| _53_342 -> begin
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

# 345 "FStar.TypeChecker.Env.fst"
let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| None -> begin
false
end
| Some (_53_352) -> begin
true
end))

# 349 "FStar.TypeChecker.Env.fst"
let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _53_358, _53_360, _53_362) -> begin
(add_sigelts env ses)
end
| _53_366 -> begin
(
# 354 "FStar.TypeChecker.Env.fst"
let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _132_534 = (sigtab env)
in (FStar_Util.smap_add _132_534 l.FStar_Ident.str se))) lids))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))

# 358 "FStar.TypeChecker.Env.fst"
let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun _53_3 -> (match (_53_3) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _53_377 -> begin
None
end))))

# 367 "FStar.TypeChecker.Env.fst"
let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _53_4 -> (match (_53_4) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _53_384 -> begin
false
end)) env.gamma) FStar_Option.isSome))

# 373 "FStar.TypeChecker.Env.fst"
let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_53_388, lb::[]), _53_393, _53_395, _53_397) -> begin
(let _132_554 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_132_554))
end
| FStar_Syntax_Syntax.Sig_let ((_53_401, lbs), _53_405, _53_407, _53_409) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_53_414) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _132_556 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_132_556))
end else begin
None
end
end)))
end
| _53_419 -> begin
None
end))

# 387 "FStar.TypeChecker.Env.fst"
let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _132_564 = (let _132_563 = (let _132_562 = (variable_not_found bv)
in (let _132_561 = (FStar_Syntax_Syntax.range_of_bv bv)
in (_132_562, _132_561)))
in FStar_Syntax_Syntax.Error (_132_563))
in (Prims.raise _132_564))
end
| Some (t) -> begin
t
end))

# 392 "FStar.TypeChecker.Env.fst"
let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _53_428) -> begin
(let _132_570 = (let _132_569 = (let _132_568 = (let _132_567 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _132_567))
in (ne.FStar_Syntax_Syntax.univs, _132_568))
in (inst_tscheme _132_569))
in Some (_132_570))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _53_435, _53_437, _53_439) -> begin
(let _132_574 = (let _132_573 = (let _132_572 = (let _132_571 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _132_571))
in (us, _132_572))
in (inst_tscheme _132_573))
in Some (_132_574))
end
| _53_443 -> begin
None
end))

# 402 "FStar.TypeChecker.Env.fst"
let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_53_453, t) -> begin
Some (t)
end)
end
| _53_458 -> begin
None
end))

# 411 "FStar.TypeChecker.Env.fst"
let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env lid -> (
# 414 "FStar.TypeChecker.Env.fst"
let mapper = (fun _53_5 -> (match (_53_5) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_53_465, uvs, t, _53_469, _53_471, _53_473, _53_475, _53_477), None) -> begin
(let _132_585 = (inst_tscheme (uvs, t))
in Some (_132_585))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _53_488), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _132_586 = (inst_tscheme (uvs, t))
in Some (_132_586))
end else begin
None
end
end else begin
(let _132_587 = (inst_tscheme (uvs, t))
in Some (_132_587))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _53_499, _53_501, _53_503, _53_505), None) -> begin
(match (tps) with
| [] -> begin
(let _132_589 = (inst_tscheme (uvs, k))
in (FStar_All.pipe_left (fun _132_588 -> Some (_132_588)) _132_589))
end
| _53_513 -> begin
(let _132_594 = (let _132_593 = (let _132_592 = (let _132_591 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _132_591))
in (uvs, _132_592))
in (inst_tscheme _132_593))
in (FStar_All.pipe_left (fun _132_590 -> Some (_132_590)) _132_594))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _53_519, _53_521, _53_523, _53_525), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _132_596 = (inst_tscheme_with (uvs, k) us)
in (FStar_All.pipe_left (fun _132_595 -> Some (_132_595)) _132_596))
end
| _53_534 -> begin
(let _132_601 = (let _132_600 = (let _132_599 = (let _132_598 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _132_598))
in (uvs, _132_599))
in (inst_tscheme_with _132_600 us))
in (FStar_All.pipe_left (fun _132_597 -> Some (_132_597)) _132_601))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_53_538), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _53_543 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _132_602 = (lookup_qname env lid)
in (FStar_Util.bind_opt _132_602 mapper))) with
| Some (us, t) -> begin
Some ((us, (
# 448 "FStar.TypeChecker.Env.fst"
let _53_549 = t
in {FStar_Syntax_Syntax.n = _53_549.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_549.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _53_549.FStar_Syntax_Syntax.vars})))
end
| None -> begin
None
end)))

# 449 "FStar.TypeChecker.Env.fst"
let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (
# 452 "FStar.TypeChecker.Env.fst"
let mapper = (fun _53_6 -> (match (_53_6) with
| FStar_Util.Inl (_53_556) -> begin
Some (false)
end
| FStar_Util.Inr (se, _53_560) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (_53_564, _53_566, _53_568, qs, _53_571) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (_53_575) -> begin
Some (true)
end
| _53_578 -> begin
Some (false)
end)
end))
in (match ((let _132_609 = (lookup_qname env lid)
in (FStar_Util.bind_opt _132_609 mapper))) with
| Some (b) -> begin
b
end
| None -> begin
false
end)))

# 464 "FStar.TypeChecker.Env.fst"
let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _132_616 = (let _132_615 = (let _132_614 = (name_not_found l)
in (_132_614, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_132_615))
in (Prims.raise _132_616))
end
| Some (x) -> begin
x
end))

# 470 "FStar.TypeChecker.Env.fst"
let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_53_591, uvs, t, _53_595, _53_597), None)) -> begin
(inst_tscheme (uvs, t))
end
| _53_605 -> begin
(let _132_623 = (let _132_622 = (let _132_621 = (name_not_found lid)
in (_132_621, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_132_622))
in (Prims.raise _132_623))
end))

# 475 "FStar.TypeChecker.Env.fst"
let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_53_609, uvs, t, _53_613, _53_615, _53_617, _53_619, _53_621), None)) -> begin
(inst_tscheme (uvs, t))
end
| _53_629 -> begin
(let _132_630 = (let _132_629 = (let _132_628 = (name_not_found lid)
in (_132_628, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_132_629))
in (Prims.raise _132_630))
end))

# 480 "FStar.TypeChecker.Env.fst"
let lookup_definition : delta_level  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_53_639, lbs), _53_643, _53_645, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (
# 488 "FStar.TypeChecker.Env.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _132_639 = (let _132_638 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (lb.FStar_Syntax_Syntax.lbunivs, _132_638))
in Some (_132_639))
end else begin
None
end)))
end
| _53_652 -> begin
None
end)
end
| _53_654 -> begin
None
end))

# 494 "FStar.TypeChecker.Env.fst"
let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _132_646 = (let _132_645 = (let _132_644 = (name_not_found ftv)
in (_132_644, (FStar_Ident.range_of_lid ftv)))
in FStar_Syntax_Syntax.Error (_132_645))
in (Prims.raise _132_646))
end
| Some (k) -> begin
k
end))

# 499 "FStar.TypeChecker.Env.fst"
let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (
# 502 "FStar.TypeChecker.Env.fst"
let fail = (fun _53_664 -> (match (()) with
| () -> begin
(let _132_657 = (let _132_656 = (FStar_Util.string_of_int i)
in (let _132_655 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _132_656 _132_655)))
in (FStar_All.failwith _132_657))
end))
in (
# 503 "FStar.TypeChecker.Env.fst"
let _53_668 = (lookup_datacon env lid)
in (match (_53_668) with
| (_53_666, t) -> begin
(match ((let _132_658 = (FStar_Syntax_Subst.compress t)
in _132_658.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _53_671) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(
# 508 "FStar.TypeChecker.Env.fst"
let b = (FStar_List.nth binders i)
in (let _132_659 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _132_659 Prims.fst)))
end
end
| _53_676 -> begin
(fail ())
end)
end))))

# 510 "FStar.TypeChecker.Env.fst"
let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_53_680, uvs, t, q, _53_685), None)) -> begin
Some (((uvs, t), q))
end
| _53_693 -> begin
None
end))

# 515 "FStar.TypeChecker.Env.fst"
let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _53_703), None)) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_7 -> (match (_53_7) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _53_713 -> begin
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
| ([], _53_717) -> begin
(FStar_All.failwith "Unexpected effect abbreviation with no arguments")
end
| (_53_720, _53_727::_53_724::_53_722) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(let _132_673 = (let _132_672 = (FStar_Syntax_Print.lid_to_string lid)
in (let _132_671 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _132_672 _132_671)))
in (FStar_All.failwith _132_673))
end
| _53_731 -> begin
(
# 530 "FStar.TypeChecker.Env.fst"
let _53_735 = (let _132_675 = (let _132_674 = (FStar_Syntax_Util.arrow binders c)
in (univs, _132_674))
in (inst_tscheme_with _132_675 insts))
in (match (_53_735) with
| (_53_733, t) -> begin
(match ((let _132_676 = (FStar_Syntax_Subst.compress t)
in _132_676.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some ((binders, c))
end
| _53_741 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end))
end
end
| _53_743 -> begin
None
end))

# 537 "FStar.TypeChecker.Env.fst"
let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_53_747, _53_749, _53_751, _53_753, _53_755, dcs, _53_758, _53_760), _53_764)) -> begin
dcs
end
| _53_769 -> begin
[]
end))

# 542 "FStar.TypeChecker.Env.fst"
let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_53_773, _53_775, _53_777, l, _53_780, _53_782, _53_784, _53_786), _53_790)) -> begin
l
end
| _53_795 -> begin
(let _132_686 = (let _132_685 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _132_685))
in (FStar_All.failwith _132_686))
end))

# 547 "FStar.TypeChecker.Env.fst"
let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_53_799, _53_801, _53_803, _53_805, _53_807, _53_809, _53_811, _53_813), _53_817)) -> begin
true
end
| _53_822 -> begin
false
end))

# 552 "FStar.TypeChecker.Env.fst"
let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_53_826, _53_828, _53_830, _53_832, _53_834, _53_836, tags, _53_839), _53_843)) -> begin
(FStar_Util.for_some (fun _53_8 -> (match (_53_8) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _53_855 -> begin
false
end)) tags)
end
| _53_857 -> begin
false
end))

# 558 "FStar.TypeChecker.Env.fst"
let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_53_861, _53_863, _53_865, quals, _53_868), _53_872)) -> begin
(FStar_Util.for_some (fun _53_9 -> (match (_53_9) with
| FStar_Syntax_Syntax.Projector (_53_878) -> begin
true
end
| _53_881 -> begin
false
end)) quals)
end
| _53_883 -> begin
false
end))

# 564 "FStar.TypeChecker.Env.fst"
let interpreted_symbols : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]

# 581 "FStar.TypeChecker.Env.fst"
let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env head -> (match ((let _132_705 = (FStar_Syntax_Util.un_uinst head)
in _132_705.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _53_889 -> begin
false
end))

# 588 "FStar.TypeChecker.Env.fst"
let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))

# 594 "FStar.TypeChecker.Env.fst"
let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _132_717 = (let _132_716 = (let _132_715 = (name_not_found l)
in (_132_715, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_132_716))
in (Prims.raise _132_717))
end
| Some (md) -> begin
md
end))

# 599 "FStar.TypeChecker.Env.fst"
let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
(l1, (fun t wp -> wp), (fun t wp -> wp))
end else begin
if (((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid))) then begin
(FStar_Syntax_Const.effect_GTot_lid, (fun t wp -> wp), (fun t wp -> wp))
end else begin
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _53_917 -> (match (_53_917) with
| (m1, m2, _53_912, _53_914, _53_916) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _132_793 = (let _132_792 = (let _132_791 = (let _132_790 = (FStar_Syntax_Print.lid_to_string l1)
in (let _132_789 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _132_790 _132_789)))
in (_132_791, env.range))
in FStar_Syntax_Syntax.Error (_132_792))
in (Prims.raise _132_793))
end
| Some (_53_920, _53_922, m3, j1, j2) -> begin
(m3, j1, j2)
end)
end
end)

# 609 "FStar.TypeChecker.Env.fst"
let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge Prims.option = (fun env l1 l2 -> if ((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid))) then begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end else begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end)

# 615 "FStar.TypeChecker.Env.fst"
let wp_sig_aux : FStar_Syntax_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun decls m -> (match ((FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))))) with
| None -> begin
(let _132_808 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _132_808))
end
| Some (md) -> begin
(
# 621 "FStar.TypeChecker.Env.fst"
let _53_943 = (inst_tscheme (md.FStar_Syntax_Syntax.univs, md.FStar_Syntax_Syntax.signature))
in (match (_53_943) with
| (_53_941, s) -> begin
(
# 622 "FStar.TypeChecker.Env.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match ((md.FStar_Syntax_Syntax.binders, s.FStar_Syntax_Syntax.n)) with
| ([], FStar_Syntax_Syntax.Tm_arrow ((a, _53_956)::(wp, _53_952)::(wlp, _53_948)::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _53_964 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))

# 625 "FStar.TypeChecker.Env.fst"
let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))

# 627 "FStar.TypeChecker.Env.fst"
let default_effect : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (FStar_Util.find_map env.default_effects (fun _53_971 -> (match (_53_971) with
| (l', m) -> begin
if (FStar_Ident.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))

# 629 "FStar.TypeChecker.Env.fst"
let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, _53_976, _53_978, c, quals, r) -> begin
(match ((FStar_Util.find_map quals (fun _53_10 -> (match (_53_10) with
| FStar_Syntax_Syntax.DefaultEffect (n) -> begin
n
end
| _53_988 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(
# 635 "FStar.TypeChecker.Env.fst"
let _53_992 = env
in {solver = _53_992.solver; range = _53_992.range; curmodule = _53_992.curmodule; gamma = _53_992.gamma; gamma_cache = _53_992.gamma_cache; modules = _53_992.modules; expected_typ = _53_992.expected_typ; sigtab = _53_992.sigtab; is_pattern = _53_992.is_pattern; instantiate_imp = _53_992.instantiate_imp; effects = _53_992.effects; generalize = _53_992.generalize; letrecs = _53_992.letrecs; top_level = _53_992.top_level; check_uvars = _53_992.check_uvars; use_eq = _53_992.use_eq; is_iface = _53_992.is_iface; admit = _53_992.admit; default_effects = ((e, l))::env.default_effects; type_of = _53_992.type_of; universe_of = _53_992.universe_of; use_bv_sorts = _53_992.use_bv_sorts})
end)
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _53_996) -> begin
(
# 638 "FStar.TypeChecker.Env.fst"
let effects = (
# 638 "FStar.TypeChecker.Env.fst"
let _53_999 = env.effects
in {decls = (ne)::env.effects.decls; order = _53_999.order; joins = _53_999.joins})
in (
# 639 "FStar.TypeChecker.Env.fst"
let _53_1002 = env
in {solver = _53_1002.solver; range = _53_1002.range; curmodule = _53_1002.curmodule; gamma = _53_1002.gamma; gamma_cache = _53_1002.gamma_cache; modules = _53_1002.modules; expected_typ = _53_1002.expected_typ; sigtab = _53_1002.sigtab; is_pattern = _53_1002.is_pattern; instantiate_imp = _53_1002.instantiate_imp; effects = effects; generalize = _53_1002.generalize; letrecs = _53_1002.letrecs; top_level = _53_1002.top_level; check_uvars = _53_1002.check_uvars; use_eq = _53_1002.use_eq; is_iface = _53_1002.is_iface; admit = _53_1002.admit; default_effects = _53_1002.default_effects; type_of = _53_1002.type_of; universe_of = _53_1002.universe_of; use_bv_sorts = _53_1002.use_bv_sorts}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _53_1006) -> begin
(
# 642 "FStar.TypeChecker.Env.fst"
let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _132_829 = (e1.mlift r wp1)
in (e2.mlift r _132_829)))})
in (
# 647 "FStar.TypeChecker.Env.fst"
let mk_lift = (fun lift_t r wp1 -> (
# 648 "FStar.TypeChecker.Env.fst"
let _53_1021 = (inst_tscheme lift_t)
in (match (_53_1021) with
| (_53_1019, lift_t) -> begin
(let _132_841 = (let _132_840 = (let _132_839 = (let _132_838 = (FStar_Syntax_Syntax.as_arg r)
in (let _132_837 = (let _132_836 = (FStar_Syntax_Syntax.as_arg wp1)
in (_132_836)::[])
in (_132_838)::_132_837))
in (lift_t, _132_839))
in FStar_Syntax_Syntax.Tm_app (_132_840))
in (FStar_Syntax_Syntax.mk _132_841 None wp1.FStar_Syntax_Syntax.pos))
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
let arg = (let _132_858 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _132_858 FStar_Syntax_Syntax.Delta_constant None))
in (
# 662 "FStar.TypeChecker.Env.fst"
let wp = (let _132_859 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _132_859 FStar_Syntax_Syntax.Delta_constant None))
in (let _132_860 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _132_860)))))
in (
# 664 "FStar.TypeChecker.Env.fst"
let order = (edge)::env.effects.order
in (
# 666 "FStar.TypeChecker.Env.fst"
let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (
# 668 "FStar.TypeChecker.Env.fst"
let find_edge = (fun order _53_1038 -> (match (_53_1038) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _132_866 -> Some (_132_866)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (
# 677 "FStar.TypeChecker.Env.fst"
let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _132_874 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _132_873 = (find_edge order (i, k))
in (let _132_872 = (find_edge order (k, j))
in (_132_873, _132_872)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _53_1050 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _132_874))) order))
in (
# 688 "FStar.TypeChecker.Env.fst"
let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (
# 690 "FStar.TypeChecker.Env.fst"
let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (
# 693 "FStar.TypeChecker.Env.fst"
let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _132_966 = (find_edge order (i, k))
in (let _132_965 = (find_edge order (j, k))
in (_132_966, _132_965)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _53_1067, _53_1069) -> begin
if ((let _132_967 = (find_edge order (k, ub))
in (FStar_Util.is_some _132_967)) && (not ((let _132_968 = (find_edge order (ub, k))
in (FStar_Util.is_some _132_968))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _53_1073 -> begin
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
let _53_1082 = env.effects
in {decls = _53_1082.decls; order = order; joins = joins})
in (
# 713 "FStar.TypeChecker.Env.fst"
let _53_1085 = env
in {solver = _53_1085.solver; range = _53_1085.range; curmodule = _53_1085.curmodule; gamma = _53_1085.gamma; gamma_cache = _53_1085.gamma_cache; modules = _53_1085.modules; expected_typ = _53_1085.expected_typ; sigtab = _53_1085.sigtab; is_pattern = _53_1085.is_pattern; instantiate_imp = _53_1085.instantiate_imp; effects = effects; generalize = _53_1085.generalize; letrecs = _53_1085.letrecs; top_level = _53_1085.top_level; check_uvars = _53_1085.check_uvars; use_eq = _53_1085.use_eq; is_iface = _53_1085.is_iface; admit = _53_1085.admit; default_effects = _53_1085.default_effects; type_of = _53_1085.type_of; universe_of = _53_1085.universe_of; use_bv_sorts = _53_1085.use_bv_sorts})))))))))))))
end
| _53_1088 -> begin
env
end))

# 715 "FStar.TypeChecker.Env.fst"
let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (let _132_1017 = (
# 720 "FStar.TypeChecker.Env.fst"
let _53_1091 = env
in (let _132_1016 = (let _132_1015 = (let _132_1014 = (let _132_1013 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_132_1013, s))
in Binding_sig (_132_1014))
in (_132_1015)::env.gamma)
in {solver = _53_1091.solver; range = _53_1091.range; curmodule = _53_1091.curmodule; gamma = _132_1016; gamma_cache = _53_1091.gamma_cache; modules = _53_1091.modules; expected_typ = _53_1091.expected_typ; sigtab = _53_1091.sigtab; is_pattern = _53_1091.is_pattern; instantiate_imp = _53_1091.instantiate_imp; effects = _53_1091.effects; generalize = _53_1091.generalize; letrecs = _53_1091.letrecs; top_level = _53_1091.top_level; check_uvars = _53_1091.check_uvars; use_eq = _53_1091.use_eq; is_iface = _53_1091.is_iface; admit = _53_1091.admit; default_effects = _53_1091.default_effects; type_of = _53_1091.type_of; universe_of = _53_1091.universe_of; use_bv_sorts = _53_1091.use_bv_sorts}))
in (build_lattice _132_1017 s)))

# 720 "FStar.TypeChecker.Env.fst"
let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (let _132_1028 = (
# 722 "FStar.TypeChecker.Env.fst"
let _53_1096 = env
in (let _132_1027 = (let _132_1026 = (let _132_1025 = (let _132_1024 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_132_1024, s, us))
in Binding_sig_inst (_132_1025))
in (_132_1026)::env.gamma)
in {solver = _53_1096.solver; range = _53_1096.range; curmodule = _53_1096.curmodule; gamma = _132_1027; gamma_cache = _53_1096.gamma_cache; modules = _53_1096.modules; expected_typ = _53_1096.expected_typ; sigtab = _53_1096.sigtab; is_pattern = _53_1096.is_pattern; instantiate_imp = _53_1096.instantiate_imp; effects = _53_1096.effects; generalize = _53_1096.generalize; letrecs = _53_1096.letrecs; top_level = _53_1096.top_level; check_uvars = _53_1096.check_uvars; use_eq = _53_1096.use_eq; is_iface = _53_1096.is_iface; admit = _53_1096.admit; default_effects = _53_1096.default_effects; type_of = _53_1096.type_of; universe_of = _53_1096.universe_of; use_bv_sorts = _53_1096.use_bv_sorts}))
in (build_lattice _132_1028 s)))

# 722 "FStar.TypeChecker.Env.fst"
let push_local_binding : env  ->  binding  ->  env = (fun env b -> (
# 724 "FStar.TypeChecker.Env.fst"
let _53_1100 = env
in {solver = _53_1100.solver; range = _53_1100.range; curmodule = _53_1100.curmodule; gamma = (b)::env.gamma; gamma_cache = _53_1100.gamma_cache; modules = _53_1100.modules; expected_typ = _53_1100.expected_typ; sigtab = _53_1100.sigtab; is_pattern = _53_1100.is_pattern; instantiate_imp = _53_1100.instantiate_imp; effects = _53_1100.effects; generalize = _53_1100.generalize; letrecs = _53_1100.letrecs; top_level = _53_1100.top_level; check_uvars = _53_1100.check_uvars; use_eq = _53_1100.use_eq; is_iface = _53_1100.is_iface; admit = _53_1100.admit; default_effects = _53_1100.default_effects; type_of = _53_1100.type_of; universe_of = _53_1100.universe_of; use_bv_sorts = _53_1100.use_bv_sorts}))

# 724 "FStar.TypeChecker.Env.fst"
let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))

# 726 "FStar.TypeChecker.Env.fst"
let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _53_1110 -> (match (_53_1110) with
| (x, _53_1109) -> begin
(push_bv env x)
end)) env bs))

# 729 "FStar.TypeChecker.Env.fst"
let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(
# 733 "FStar.TypeChecker.Env.fst"
let _53_1115 = ()
in (
# 734 "FStar.TypeChecker.Env.fst"
let x = (
# 734 "FStar.TypeChecker.Env.fst"
let _53_1117 = x
in {FStar_Syntax_Syntax.ppname = _53_1117.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1117.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, t))
end))

# 737 "FStar.TypeChecker.Env.fst"
let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))

# 740 "FStar.TypeChecker.Env.fst"
let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (
# 742 "FStar.TypeChecker.Env.fst"
let _53_1127 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (
# 743 "FStar.TypeChecker.Env.fst"
let _53_1129 = env
in {solver = _53_1129.solver; range = _53_1129.range; curmodule = _53_1129.curmodule; gamma = []; gamma_cache = _53_1129.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _53_1129.sigtab; is_pattern = _53_1129.is_pattern; instantiate_imp = _53_1129.instantiate_imp; effects = _53_1129.effects; generalize = _53_1129.generalize; letrecs = _53_1129.letrecs; top_level = _53_1129.top_level; check_uvars = _53_1129.check_uvars; use_eq = _53_1129.use_eq; is_iface = _53_1129.is_iface; admit = _53_1129.admit; default_effects = _53_1129.default_effects; type_of = _53_1129.type_of; universe_of = _53_1129.universe_of; use_bv_sorts = _53_1129.use_bv_sorts})))

# 746 "FStar.TypeChecker.Env.fst"
let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))

# 749 "FStar.TypeChecker.Env.fst"
let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (
# 752 "FStar.TypeChecker.Env.fst"
let _53_1137 = env
in {solver = _53_1137.solver; range = _53_1137.range; curmodule = _53_1137.curmodule; gamma = _53_1137.gamma; gamma_cache = _53_1137.gamma_cache; modules = _53_1137.modules; expected_typ = Some (t); sigtab = _53_1137.sigtab; is_pattern = _53_1137.is_pattern; instantiate_imp = _53_1137.instantiate_imp; effects = _53_1137.effects; generalize = _53_1137.generalize; letrecs = _53_1137.letrecs; top_level = _53_1137.top_level; check_uvars = _53_1137.check_uvars; use_eq = false; is_iface = _53_1137.is_iface; admit = _53_1137.admit; default_effects = _53_1137.default_effects; type_of = _53_1137.type_of; universe_of = _53_1137.universe_of; use_bv_sorts = _53_1137.use_bv_sorts}))

# 752 "FStar.TypeChecker.Env.fst"
let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

# 756 "FStar.TypeChecker.Env.fst"
let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _132_1071 = (expected_typ env)
in ((
# 759 "FStar.TypeChecker.Env.fst"
let _53_1144 = env
in {solver = _53_1144.solver; range = _53_1144.range; curmodule = _53_1144.curmodule; gamma = _53_1144.gamma; gamma_cache = _53_1144.gamma_cache; modules = _53_1144.modules; expected_typ = None; sigtab = _53_1144.sigtab; is_pattern = _53_1144.is_pattern; instantiate_imp = _53_1144.instantiate_imp; effects = _53_1144.effects; generalize = _53_1144.generalize; letrecs = _53_1144.letrecs; top_level = _53_1144.top_level; check_uvars = _53_1144.check_uvars; use_eq = false; is_iface = _53_1144.is_iface; admit = _53_1144.admit; default_effects = _53_1144.default_effects; type_of = _53_1144.type_of; universe_of = _53_1144.universe_of; use_bv_sorts = _53_1144.use_bv_sorts}), _132_1071)))

# 759 "FStar.TypeChecker.Env.fst"
let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (
# 762 "FStar.TypeChecker.Env.fst"
let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (
# 764 "FStar.TypeChecker.Env.fst"
let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(let _132_1077 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _53_11 -> (match (_53_11) with
| Binding_sig (_53_1151, se) -> begin
(se)::[]
end
| _53_1156 -> begin
[]
end))))
in (FStar_All.pipe_right _132_1077 FStar_List.rev))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (
# 770 "FStar.TypeChecker.Env.fst"
let _53_1158 = (add_sigelts env sigs)
in (
# 771 "FStar.TypeChecker.Env.fst"
let _53_1160 = (FStar_Util.smap_clear env.gamma_cache)
in (
# 772 "FStar.TypeChecker.Env.fst"
let _53_1162 = env
in {solver = _53_1162.solver; range = _53_1162.range; curmodule = empty_lid; gamma = []; gamma_cache = _53_1162.gamma_cache; modules = (m)::env.modules; expected_typ = _53_1162.expected_typ; sigtab = _53_1162.sigtab; is_pattern = _53_1162.is_pattern; instantiate_imp = _53_1162.instantiate_imp; effects = _53_1162.effects; generalize = _53_1162.generalize; letrecs = _53_1162.letrecs; top_level = _53_1162.top_level; check_uvars = _53_1162.check_uvars; use_eq = _53_1162.use_eq; is_iface = _53_1162.is_iface; admit = _53_1162.admit; default_effects = _53_1162.default_effects; type_of = _53_1162.type_of; universe_of = _53_1162.universe_of; use_bv_sorts = _53_1162.use_bv_sorts}))))))

# 775 "FStar.TypeChecker.Env.fst"
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
| Binding_univ (_53_1175)::tl -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _132_1089 = (let _132_1088 = (FStar_Syntax_Free.uvars t)
in (ext out _132_1088))
in (aux _132_1089 tl))
end
| (Binding_sig (_)::_) | (Binding_sig_inst (_)::_) -> begin
out
end))
in (aux no_uvs env.gamma)))))

# 790 "FStar.TypeChecker.Env.fst"
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
(let _132_1101 = (let _132_1100 = (FStar_Syntax_Free.univs t)
in (ext out _132_1100))
in (aux _132_1101 tl))
end
| Binding_sig (_53_1245)::_53_1243 -> begin
out
end))
in (aux no_univs env.gamma)))))

# 802 "FStar.TypeChecker.Env.fst"
let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _53_12 -> (match (_53_12) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))

# 810 "FStar.TypeChecker.Env.fst"
let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _132_1108 = (let _132_1107 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _132_1107 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _132_1108 FStar_List.rev)))

# 812 "FStar.TypeChecker.Env.fst"
let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))

# 814 "FStar.TypeChecker.Env.fst"
let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))

# 816 "FStar.TypeChecker.Env.fst"
let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))

# 818 "FStar.TypeChecker.Env.fst"
let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (
# 821 "FStar.TypeChecker.Env.fst"
let keys = (FStar_List.fold_left (fun keys _53_13 -> (match (_53_13) with
| Binding_sig (lids, _53_1277) -> begin
(FStar_List.append lids keys)
end
| _53_1281 -> begin
keys
end)) [] env.gamma)
in (let _132_1132 = (sigtab env)
in (FStar_Util.smap_fold _132_1132 (fun _53_1283 v keys -> (let _132_1131 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _132_1131 keys))) keys))))

# 824 "FStar.TypeChecker.Env.fst"
let dummy_solver : solver_t = {init = (fun _53_1287 -> ()); push = (fun _53_1289 -> ()); pop = (fun _53_1291 -> ()); mark = (fun _53_1293 -> ()); reset_mark = (fun _53_1295 -> ()); commit_mark = (fun _53_1297 -> ()); encode_modul = (fun _53_1299 _53_1301 -> ()); encode_sig = (fun _53_1303 _53_1305 -> ()); solve = (fun _53_1307 _53_1309 _53_1311 -> ()); is_trivial = (fun _53_1313 _53_1315 -> false); finish = (fun _53_1317 -> ()); refresh = (fun _53_1318 -> ())}

# 841 "FStar.TypeChecker.Env.fst"
let no_solver_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t))  ->  env = (fun tc -> (let _132_1168 = (FStar_Ident.lid_of_path (("dummy")::[]) FStar_Range.dummyRange)
in (initial_env tc dummy_solver _132_1168)))




