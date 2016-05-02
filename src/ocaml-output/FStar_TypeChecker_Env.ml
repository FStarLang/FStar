
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
| Binding_var (_52_17) -> begin
_52_17
end))

# 32 "FStar.TypeChecker.Env.fst"
let ___Binding_lid____0 = (fun projectee -> (match (projectee) with
| Binding_lid (_52_20) -> begin
_52_20
end))

# 33 "FStar.TypeChecker.Env.fst"
let ___Binding_sig____0 = (fun projectee -> (match (projectee) with
| Binding_sig (_52_23) -> begin
_52_23
end))

# 34 "FStar.TypeChecker.Env.fst"
let ___Binding_univ____0 = (fun projectee -> (match (projectee) with
| Binding_univ (_52_26) -> begin
_52_26
end))

# 35 "FStar.TypeChecker.Env.fst"
let ___Binding_sig_inst____0 = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_52_29) -> begin
_52_29
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
| Unfold (_52_32) -> begin
_52_32
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
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; gamma_cache : cached_elt FStar_Util.smap Prims.list; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ Prims.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap Prims.list; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t); universe_of : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe; use_bv_sorts : Prims.bool} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit; solve : (Prims.unit  ->  Prims.string) Prims.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit} 
 and guard_t =
{guard_f : FStar_TypeChecker_Common.guard_formula; deferred : FStar_TypeChecker_Common.deferred; univ_ineqs : FStar_TypeChecker_Common.univ_ineq Prims.list; implicits : (Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list}

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

# 164 "FStar.TypeChecker.Env.fst"
let visible_at : delta_level  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun d q -> (match ((d, q)) with
| ((NoDelta, _)) | ((OnlyInline, FStar_Syntax_Syntax.Inline)) | ((Unfold (_), FStar_Syntax_Syntax.Inline)) | ((Unfold (_), FStar_Syntax_Syntax.Unfoldable)) -> begin
true
end
| _52_102 -> begin
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
| (FStar_Syntax_Syntax.Delta_abstract (l1), _52_151) -> begin
(aux l1 l2)
end
| (_52_154, FStar_Syntax_Syntax.Delta_abstract (l2)) -> begin
(aux l1 l2)
end))
in (let _141_387 = (aux l1 l2)
in Unfold (_141_387)))
end))

# 189 "FStar.TypeChecker.Env.fst"
let default_table_size : Prims.int = 200

# 190 "FStar.TypeChecker.Env.fst"
let new_sigtab = (fun _52_158 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))

# 191 "FStar.TypeChecker.Env.fst"
let new_gamma_cache = (fun _52_159 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))

# 193 "FStar.TypeChecker.Env.fst"
let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun tc solver module_lid -> (let _141_411 = (let _141_406 = (new_gamma_cache ())
in (_141_406)::[])
in (let _141_410 = (let _141_407 = (new_sigtab ())
in (_141_407)::[])
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _141_411; modules = []; expected_typ = None; sigtab = _141_410; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; type_of = tc; universe_of = (fun g e -> FStar_Syntax_Syntax.U_zero); use_bv_sorts = false})))

# 218 "FStar.TypeChecker.Env.fst"
let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> (FStar_List.hd env.sigtab))

# 219 "FStar.TypeChecker.Env.fst"
let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> (FStar_List.hd env.gamma_cache))

# 220 "FStar.TypeChecker.Env.fst"
let push_tabs : env  ->  env = (fun env -> (
# 221 "FStar.TypeChecker.Env.fst"
let _52_168 = env
in (let _141_423 = (let _141_419 = (let _141_418 = (gamma_cache env)
in (FStar_Util.smap_copy _141_418))
in (_141_419)::env.gamma_cache)
in (let _141_422 = (let _141_421 = (let _141_420 = (sigtab env)
in (FStar_Util.smap_copy _141_420))
in (_141_421)::env.sigtab)
in {solver = _52_168.solver; range = _52_168.range; curmodule = _52_168.curmodule; gamma = _52_168.gamma; gamma_cache = _141_423; modules = _52_168.modules; expected_typ = _52_168.expected_typ; sigtab = _141_422; is_pattern = _52_168.is_pattern; instantiate_imp = _52_168.instantiate_imp; effects = _52_168.effects; generalize = _52_168.generalize; letrecs = _52_168.letrecs; top_level = _52_168.top_level; check_uvars = _52_168.check_uvars; use_eq = _52_168.use_eq; is_iface = _52_168.is_iface; admit = _52_168.admit; type_of = _52_168.type_of; universe_of = _52_168.universe_of; use_bv_sorts = _52_168.use_bv_sorts}))))

# 224 "FStar.TypeChecker.Env.fst"
let push : env  ->  Prims.string  ->  env = (fun env msg -> (
# 225 "FStar.TypeChecker.Env.fst"
let _52_172 = (env.solver.push msg)
in (push_tabs env)))

# 227 "FStar.TypeChecker.Env.fst"
let mark : env  ->  env = (fun env -> (
# 228 "FStar.TypeChecker.Env.fst"
let _52_175 = (env.solver.mark "USER MARK")
in (push_tabs env)))

# 230 "FStar.TypeChecker.Env.fst"
let commit_mark : env  ->  env = (fun env -> (
# 231 "FStar.TypeChecker.Env.fst"
let _52_178 = (env.solver.commit_mark "USER MARK")
in (
# 232 "FStar.TypeChecker.Env.fst"
let commit_tab = (fun _52_1 -> (match (_52_1) with
| hd::_52_183::tl -> begin
(hd)::tl
end
| _52_188 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 236 "FStar.TypeChecker.Env.fst"
let _52_191 = env
in (let _141_434 = (commit_tab env.gamma_cache)
in (let _141_433 = (commit_tab env.sigtab)
in {solver = _52_191.solver; range = _52_191.range; curmodule = _52_191.curmodule; gamma = _52_191.gamma; gamma_cache = _141_434; modules = _52_191.modules; expected_typ = _52_191.expected_typ; sigtab = _141_433; is_pattern = _52_191.is_pattern; instantiate_imp = _52_191.instantiate_imp; effects = _52_191.effects; generalize = _52_191.generalize; letrecs = _52_191.letrecs; top_level = _52_191.top_level; check_uvars = _52_191.check_uvars; use_eq = _52_191.use_eq; is_iface = _52_191.is_iface; admit = _52_191.admit; type_of = _52_191.type_of; universe_of = _52_191.universe_of; use_bv_sorts = _52_191.use_bv_sorts}))))))

# 239 "FStar.TypeChecker.Env.fst"
let reset_mark : env  ->  env = (fun env -> (
# 240 "FStar.TypeChecker.Env.fst"
let _52_194 = (env.solver.reset_mark "USER MARK")
in (
# 241 "FStar.TypeChecker.Env.fst"
let _52_196 = env
in (let _141_438 = (FStar_List.tl env.gamma_cache)
in (let _141_437 = (FStar_List.tl env.sigtab)
in {solver = _52_196.solver; range = _52_196.range; curmodule = _52_196.curmodule; gamma = _52_196.gamma; gamma_cache = _141_438; modules = _52_196.modules; expected_typ = _52_196.expected_typ; sigtab = _141_437; is_pattern = _52_196.is_pattern; instantiate_imp = _52_196.instantiate_imp; effects = _52_196.effects; generalize = _52_196.generalize; letrecs = _52_196.letrecs; top_level = _52_196.top_level; check_uvars = _52_196.check_uvars; use_eq = _52_196.use_eq; is_iface = _52_196.is_iface; admit = _52_196.admit; type_of = _52_196.type_of; universe_of = _52_196.universe_of; use_bv_sorts = _52_196.use_bv_sorts})))))

# 244 "FStar.TypeChecker.Env.fst"
let pop : env  ->  Prims.string  ->  env = (fun env msg -> (
# 245 "FStar.TypeChecker.Env.fst"
let pop_tab = (fun _52_2 -> (match (_52_2) with
| ([]) | (_::[]) -> begin
(FStar_All.failwith "Too many pops")
end
| _52_207::tl -> begin
tl
end))
in (
# 250 "FStar.TypeChecker.Env.fst"
let _52_211 = (env.solver.pop msg)
in (
# 251 "FStar.TypeChecker.Env.fst"
let _52_213 = env
in (let _141_445 = (pop_tab env.gamma_cache)
in (let _141_444 = (pop_tab env.sigtab)
in {solver = _52_213.solver; range = _52_213.range; curmodule = _52_213.curmodule; gamma = _52_213.gamma; gamma_cache = _141_445; modules = _52_213.modules; expected_typ = _52_213.expected_typ; sigtab = _141_444; is_pattern = _52_213.is_pattern; instantiate_imp = _52_213.instantiate_imp; effects = _52_213.effects; generalize = _52_213.generalize; letrecs = _52_213.letrecs; top_level = _52_213.top_level; check_uvars = _52_213.check_uvars; use_eq = _52_213.use_eq; is_iface = _52_213.is_iface; admit = _52_213.admit; type_of = _52_213.type_of; universe_of = _52_213.universe_of; use_bv_sorts = _52_213.use_bv_sorts}))))))

# 258 "FStar.TypeChecker.Env.fst"
let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> ((let _141_451 = (FStar_ST.read FStar_Options.debug)
in (FStar_All.pipe_right _141_451 (FStar_Util.for_some (fun x -> ((env.curmodule.FStar_Ident.str = "") || (env.curmodule.FStar_Ident.str = x)))))) && (FStar_Options.debug_level_geq l)))

# 261 "FStar.TypeChecker.Env.fst"
let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(
# 261 "FStar.TypeChecker.Env.fst"
let _52_220 = e
in {solver = _52_220.solver; range = r; curmodule = _52_220.curmodule; gamma = _52_220.gamma; gamma_cache = _52_220.gamma_cache; modules = _52_220.modules; expected_typ = _52_220.expected_typ; sigtab = _52_220.sigtab; is_pattern = _52_220.is_pattern; instantiate_imp = _52_220.instantiate_imp; effects = _52_220.effects; generalize = _52_220.generalize; letrecs = _52_220.letrecs; top_level = _52_220.top_level; check_uvars = _52_220.check_uvars; use_eq = _52_220.use_eq; is_iface = _52_220.is_iface; admit = _52_220.admit; type_of = _52_220.type_of; universe_of = _52_220.universe_of; use_bv_sorts = _52_220.use_bv_sorts})
end)

# 262 "FStar.TypeChecker.Env.fst"
let get_range : env  ->  FStar_Range.range = (fun e -> e.range)

# 267 "FStar.TypeChecker.Env.fst"
let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)

# 268 "FStar.TypeChecker.Env.fst"
let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)

# 269 "FStar.TypeChecker.Env.fst"
let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (
# 269 "FStar.TypeChecker.Env.fst"
let _52_227 = env
in {solver = _52_227.solver; range = _52_227.range; curmodule = lid; gamma = _52_227.gamma; gamma_cache = _52_227.gamma_cache; modules = _52_227.modules; expected_typ = _52_227.expected_typ; sigtab = _52_227.sigtab; is_pattern = _52_227.is_pattern; instantiate_imp = _52_227.instantiate_imp; effects = _52_227.effects; generalize = _52_227.generalize; letrecs = _52_227.letrecs; top_level = _52_227.top_level; check_uvars = _52_227.check_uvars; use_eq = _52_227.use_eq; is_iface = _52_227.is_iface; admit = _52_227.admit; type_of = _52_227.type_of; universe_of = _52_227.universe_of; use_bv_sorts = _52_227.use_bv_sorts}))

# 270 "FStar.TypeChecker.Env.fst"
let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))

# 271 "FStar.TypeChecker.Env.fst"
let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (let _141_475 = (sigtab env)
in (FStar_Util.smap_try_find _141_475 (FStar_Ident.text_of_lid lid))))

# 273 "FStar.TypeChecker.Env.fst"
let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))

# 276 "FStar.TypeChecker.Env.fst"
let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _141_480 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _141_480)))

# 280 "FStar.TypeChecker.Env.fst"
let new_u_univ = (fun _52_236 -> (let _141_482 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_141_482)))

# 283 "FStar.TypeChecker.Env.fst"
let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match ((ts, us)) with
| (([], t), []) -> begin
([], t)
end
| ((formals, t), _52_249) -> begin
(
# 287 "FStar.TypeChecker.Env.fst"
let _52_251 = ()
in (
# 288 "FStar.TypeChecker.Env.fst"
let n = ((FStar_List.length formals) - 1)
in (
# 289 "FStar.TypeChecker.Env.fst"
let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN (((n - i), u)))))
in (let _141_489 = (FStar_Syntax_Subst.subst vs t)
in (us, _141_489)))))
end))

# 293 "FStar.TypeChecker.Env.fst"
let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _52_3 -> (match (_52_3) with
| ([], t) -> begin
([], t)
end
| (us, t) -> begin
(
# 296 "FStar.TypeChecker.Env.fst"
let us' = (FStar_All.pipe_right us (FStar_List.map (fun _52_264 -> (new_u_univ ()))))
in (inst_tscheme_with (us, t) us'))
end))

# 299 "FStar.TypeChecker.Env.fst"
let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed _52_272 -> (match (_52_272) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(
# 302 "FStar.TypeChecker.Env.fst"
let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in (
# 303 "FStar.TypeChecker.Env.fst"
let _52_275 = if ((FStar_List.length insts) <> (FStar_List.length univs)) then begin
(let _141_505 = (let _141_504 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _141_503 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _141_502 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _141_501 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _141_504 _141_503 _141_502 _141_501)))))
in (FStar_All.failwith _141_505))
end else begin
()
end
in (let _141_506 = (inst_tscheme_with ((FStar_List.append ed.FStar_Syntax_Syntax.univs us), t) insts)
in (Prims.snd _141_506))))
end
| _52_278 -> begin
(let _141_508 = (let _141_507 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _141_507))
in (FStar_All.failwith _141_508))
end)
end))

# 310 "FStar.TypeChecker.Env.fst"
type tri =
| Yes
| No
| Maybe

# 311 "FStar.TypeChecker.Env.fst"
let is_Yes = (fun _discr_ -> (match (_discr_) with
| Yes (_) -> begin
true
end
| _ -> begin
false
end))

# 312 "FStar.TypeChecker.Env.fst"
let is_No = (fun _discr_ -> (match (_discr_) with
| No (_) -> begin
true
end
| _ -> begin
false
end))

# 313 "FStar.TypeChecker.Env.fst"
let is_Maybe = (fun _discr_ -> (match (_discr_) with
| Maybe (_) -> begin
true
end
| _ -> begin
false
end))

# 315 "FStar.TypeChecker.Env.fst"
let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (
# 316 "FStar.TypeChecker.Env.fst"
let cur = (current_module env)
in if (l.FStar_Ident.nsstr = cur.FStar_Ident.str) then begin
Yes
end else begin
if (FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str) then begin
(
# 319 "FStar.TypeChecker.Env.fst"
let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (
# 320 "FStar.TypeChecker.Env.fst"
let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (
# 321 "FStar.TypeChecker.Env.fst"
let rec aux = (fun c l -> (match ((c, l)) with
| ([], _52_289) -> begin
Maybe
end
| (_52_292, []) -> begin
No
end
| (hd::tl, hd'::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _52_303 -> begin
No
end))
in (aux cur lns))))
end else begin
No
end
end))

# 329 "FStar.TypeChecker.Env.fst"
let lookup_qname : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either Prims.option = (fun env lid -> (
# 330 "FStar.TypeChecker.Env.fst"
let cur_mod = (in_cur_mod env lid)
in (
# 331 "FStar.TypeChecker.Env.fst"
let cache = (fun t -> (
# 331 "FStar.TypeChecker.Env.fst"
let _52_309 = (let _141_526 = (gamma_cache env)
in (FStar_Util.smap_add _141_526 lid.FStar_Ident.str t))
in Some (t)))
in (
# 332 "FStar.TypeChecker.Env.fst"
let found = if (cur_mod <> No) then begin
(match ((let _141_527 = (gamma_cache env)
in (FStar_Util.smap_try_find _141_527 lid.FStar_Ident.str))) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _52_4 -> (match (_52_4) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _141_530 = (let _141_529 = (inst_tscheme t)
in FStar_Util.Inl (_141_529))
in Some (_141_530))
end else begin
None
end
end
| Binding_sig (_52_318, FStar_Syntax_Syntax.Sig_bundle (ses, _52_321, _52_323, _52_325)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _141_532 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _141_532 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr ((se, None))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(
# 343 "FStar.TypeChecker.Env.fst"
let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_338) -> begin
Some (t)
end
| _52_341 -> begin
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
| _52_348 -> begin
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

# 360 "FStar.TypeChecker.Env.fst"
let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| None -> begin
false
end
| Some (_52_358) -> begin
true
end))

# 364 "FStar.TypeChecker.Env.fst"
let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _52_364, _52_366, _52_368) -> begin
(add_sigelts env ses)
end
| _52_372 -> begin
(
# 367 "FStar.TypeChecker.Env.fst"
let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _141_546 = (sigtab env)
in (FStar_Util.smap_add _141_546 l.FStar_Ident.str se))) lids))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))

# 376 "FStar.TypeChecker.Env.fst"
let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun _52_5 -> (match (_52_5) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _52_383 -> begin
None
end))))

# 382 "FStar.TypeChecker.Env.fst"
let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _52_6 -> (match (_52_6) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _52_390 -> begin
false
end)) env.gamma) FStar_Option.isSome))

# 388 "FStar.TypeChecker.Env.fst"
let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_394, lb::[]), _52_399, _52_401, _52_403) -> begin
(let _141_566 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_141_566))
end
| FStar_Syntax_Syntax.Sig_let ((_52_407, lbs), _52_411, _52_413, _52_415) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_52_420) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _141_568 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_141_568))
end else begin
None
end
end)))
end
| _52_425 -> begin
None
end))

# 402 "FStar.TypeChecker.Env.fst"
let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _141_576 = (let _141_575 = (let _141_574 = (variable_not_found bv)
in (let _141_573 = (FStar_Syntax_Syntax.range_of_bv bv)
in (_141_574, _141_573)))
in FStar_Syntax_Syntax.Error (_141_575))
in (Prims.raise _141_576))
end
| Some (t) -> begin
t
end))

# 407 "FStar.TypeChecker.Env.fst"
let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_434) -> begin
(let _141_582 = (let _141_581 = (let _141_580 = (let _141_579 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _141_579))
in (ne.FStar_Syntax_Syntax.univs, _141_580))
in (inst_tscheme _141_581))
in Some (_141_582))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _52_441, _52_443, _52_445) -> begin
(let _141_586 = (let _141_585 = (let _141_584 = (let _141_583 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _141_583))
in (us, _141_584))
in (inst_tscheme _141_585))
in Some (_141_586))
end
| _52_449 -> begin
None
end))

# 417 "FStar.TypeChecker.Env.fst"
let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_52_459, t) -> begin
Some (t)
end)
end
| _52_464 -> begin
None
end))

# 426 "FStar.TypeChecker.Env.fst"
let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env lid -> (
# 427 "FStar.TypeChecker.Env.fst"
let mapper = (fun _52_7 -> (match (_52_7) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_471, uvs, t, _52_475, _52_477, _52_479, _52_481, _52_483), None) -> begin
(let _141_597 = (inst_tscheme (uvs, t))
in Some (_141_597))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _52_494), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _141_598 = (inst_tscheme (uvs, t))
in Some (_141_598))
end else begin
None
end
end else begin
(let _141_599 = (inst_tscheme (uvs, t))
in Some (_141_599))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_505, _52_507, _52_509, _52_511), None) -> begin
(match (tps) with
| [] -> begin
(let _141_601 = (inst_tscheme (uvs, k))
in (FStar_All.pipe_left (fun _141_600 -> Some (_141_600)) _141_601))
end
| _52_519 -> begin
(let _141_606 = (let _141_605 = (let _141_604 = (let _141_603 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _141_603))
in (uvs, _141_604))
in (inst_tscheme _141_605))
in (FStar_All.pipe_left (fun _141_602 -> Some (_141_602)) _141_606))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_525, _52_527, _52_529, _52_531), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _141_608 = (inst_tscheme_with (uvs, k) us)
in (FStar_All.pipe_left (fun _141_607 -> Some (_141_607)) _141_608))
end
| _52_540 -> begin
(let _141_613 = (let _141_612 = (let _141_611 = (let _141_610 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _141_610))
in (uvs, _141_611))
in (inst_tscheme_with _141_612 us))
in (FStar_All.pipe_left (fun _141_609 -> Some (_141_609)) _141_613))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_52_544), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _52_549 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _141_614 = (lookup_qname env lid)
in (FStar_Util.bind_opt _141_614 mapper))) with
| Some (us, t) -> begin
Some ((us, (
# 461 "FStar.TypeChecker.Env.fst"
let _52_555 = t
in {FStar_Syntax_Syntax.n = _52_555.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _52_555.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _52_555.FStar_Syntax_Syntax.vars})))
end
| None -> begin
None
end)))

# 464 "FStar.TypeChecker.Env.fst"
let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (
# 465 "FStar.TypeChecker.Env.fst"
let mapper = (fun _52_8 -> (match (_52_8) with
| FStar_Util.Inl (_52_562) -> begin
Some (false)
end
| FStar_Util.Inr (se, _52_566) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_570, _52_572, _52_574, qs, _52_577) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (_52_581) -> begin
Some (true)
end
| _52_584 -> begin
Some (false)
end)
end))
in (match ((let _141_621 = (lookup_qname env lid)
in (FStar_Util.bind_opt _141_621 mapper))) with
| Some (b) -> begin
b
end
| None -> begin
false
end)))

# 480 "FStar.TypeChecker.Env.fst"
let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _141_628 = (let _141_627 = (let _141_626 = (name_not_found l)
in (_141_626, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_141_627))
in (Prims.raise _141_628))
end
| Some (x) -> begin
x
end))

# 485 "FStar.TypeChecker.Env.fst"
let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_597, uvs, t, _52_601, _52_603), None)) -> begin
(inst_tscheme (uvs, t))
end
| _52_611 -> begin
(let _141_635 = (let _141_634 = (let _141_633 = (name_not_found lid)
in (_141_633, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_141_634))
in (Prims.raise _141_635))
end))

# 490 "FStar.TypeChecker.Env.fst"
let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_615, uvs, t, _52_619, _52_621, _52_623, _52_625, _52_627), None)) -> begin
(inst_tscheme (uvs, t))
end
| _52_635 -> begin
(let _141_642 = (let _141_641 = (let _141_640 = (name_not_found lid)
in (_141_640, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_141_641))
in (Prims.raise _141_642))
end))

# 495 "FStar.TypeChecker.Env.fst"
let lookup_definition : delta_level  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_645, lbs), _52_649, _52_651, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (
# 501 "FStar.TypeChecker.Env.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _141_651 = (let _141_650 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (lb.FStar_Syntax_Syntax.lbunivs, _141_650))
in Some (_141_651))
end else begin
None
end)))
end
| _52_658 -> begin
None
end)
end
| _52_660 -> begin
None
end))

# 509 "FStar.TypeChecker.Env.fst"
let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _141_658 = (let _141_657 = (let _141_656 = (name_not_found ftv)
in (_141_656, (FStar_Ident.range_of_lid ftv)))
in FStar_Syntax_Syntax.Error (_141_657))
in (Prims.raise _141_658))
end
| Some (k) -> begin
k
end))

# 514 "FStar.TypeChecker.Env.fst"
let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (
# 515 "FStar.TypeChecker.Env.fst"
let fail = (fun _52_670 -> (match (()) with
| () -> begin
(let _141_669 = (let _141_668 = (FStar_Util.string_of_int i)
in (let _141_667 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _141_668 _141_667)))
in (FStar_All.failwith _141_669))
end))
in (
# 516 "FStar.TypeChecker.Env.fst"
let _52_674 = (lookup_datacon env lid)
in (match (_52_674) with
| (_52_672, t) -> begin
(match ((let _141_670 = (FStar_Syntax_Subst.compress t)
in _141_670.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _52_677) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(
# 521 "FStar.TypeChecker.Env.fst"
let b = (FStar_List.nth binders i)
in (let _141_671 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _141_671 Prims.fst)))
end
end
| _52_682 -> begin
(fail ())
end)
end))))

# 525 "FStar.TypeChecker.Env.fst"
let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_686, uvs, t, q, _52_691), None)) -> begin
Some (((uvs, t), q))
end
| _52_699 -> begin
None
end))

# 530 "FStar.TypeChecker.Env.fst"
let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _52_709), None)) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _52_9 -> (match (_52_9) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _52_719 -> begin
false
end)))) then begin
None
end else begin
(
# 535 "FStar.TypeChecker.Env.fst"
let insts = if (FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid) then begin
(univ)::(FStar_Syntax_Syntax.U_zero)::[]
end else begin
(univ)::[]
end
in (match ((binders, univs)) with
| ([], _52_723) -> begin
(FStar_All.failwith "Unexpected effect abbreviation with no arguments")
end
| (_52_726, _52_733::_52_730::_52_728) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(let _141_685 = (let _141_684 = (FStar_Syntax_Print.lid_to_string lid)
in (let _141_683 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _141_684 _141_683)))
in (FStar_All.failwith _141_685))
end
| _52_737 -> begin
(
# 543 "FStar.TypeChecker.Env.fst"
let _52_741 = (let _141_687 = (let _141_686 = (FStar_Syntax_Util.arrow binders c)
in (univs, _141_686))
in (inst_tscheme_with _141_687 insts))
in (match (_52_741) with
| (_52_739, t) -> begin
(match ((let _141_688 = (FStar_Syntax_Subst.compress t)
in _141_688.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some ((binders, c))
end
| _52_747 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end))
end
end
| _52_749 -> begin
None
end))

# 552 "FStar.TypeChecker.Env.fst"
let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (
# 553 "FStar.TypeChecker.Env.fst"
let cache = (FStar_Util.smap_create 20)
in (fun env l -> (
# 555 "FStar.TypeChecker.Env.fst"
let rec find = (fun l -> (match ((lookup_effect_abbrev env FStar_Syntax_Syntax.U_unknown l)) with
| None -> begin
None
end
| Some (_52_757, c) -> begin
(
# 559 "FStar.TypeChecker.Env.fst"
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
# 563 "FStar.TypeChecker.Env.fst"
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
# 568 "FStar.TypeChecker.Env.fst"
let _52_771 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

# 573 "FStar.TypeChecker.Env.fst"
let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_777, _52_779, _52_781, _52_783, _52_785, dcs, _52_788, _52_790), _52_794)) -> begin
dcs
end
| _52_799 -> begin
[]
end))

# 578 "FStar.TypeChecker.Env.fst"
let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_803, _52_805, _52_807, l, _52_810, _52_812, _52_814, _52_816), _52_820)) -> begin
l
end
| _52_825 -> begin
(let _141_704 = (let _141_703 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _141_703))
in (FStar_All.failwith _141_704))
end))

# 583 "FStar.TypeChecker.Env.fst"
let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_829, _52_831, _52_833, _52_835, _52_837, _52_839, _52_841, _52_843), _52_847)) -> begin
true
end
| _52_852 -> begin
false
end))

# 588 "FStar.TypeChecker.Env.fst"
let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_856, _52_858, _52_860, _52_862, _52_864, _52_866, tags, _52_869), _52_873)) -> begin
(FStar_Util.for_some (fun _52_10 -> (match (_52_10) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _52_885 -> begin
false
end)) tags)
end
| _52_887 -> begin
false
end))

# 594 "FStar.TypeChecker.Env.fst"
let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_891, _52_893, _52_895, quals, _52_898), _52_902)) -> begin
(FStar_Util.for_some (fun _52_11 -> (match (_52_11) with
| FStar_Syntax_Syntax.Projector (_52_908) -> begin
true
end
| _52_911 -> begin
false
end)) quals)
end
| _52_913 -> begin
false
end))

# 600 "FStar.TypeChecker.Env.fst"
let interpreted_symbols : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]

# 617 "FStar.TypeChecker.Env.fst"
let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env head -> (match ((let _141_723 = (FStar_Syntax_Util.un_uinst head)
in _141_723.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _52_919 -> begin
false
end))

# 627 "FStar.TypeChecker.Env.fst"
let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))

# 630 "FStar.TypeChecker.Env.fst"
let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _141_735 = (let _141_734 = (let _141_733 = (name_not_found l)
in (_141_733, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_141_734))
in (Prims.raise _141_735))
end
| Some (md) -> begin
md
end))

# 635 "FStar.TypeChecker.Env.fst"
let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
(l1, (fun t wp -> wp), (fun t wp -> wp))
end else begin
if (((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid))) then begin
(FStar_Syntax_Const.effect_GTot_lid, (fun t wp -> wp), (fun t wp -> wp))
end else begin
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _52_947 -> (match (_52_947) with
| (m1, m2, _52_942, _52_944, _52_946) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _141_811 = (let _141_810 = (let _141_809 = (let _141_808 = (FStar_Syntax_Print.lid_to_string l1)
in (let _141_807 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _141_808 _141_807)))
in (_141_809, env.range))
in FStar_Syntax_Syntax.Error (_141_810))
in (Prims.raise _141_811))
end
| Some (_52_950, _52_952, m3, j1, j2) -> begin
(m3, j1, j2)
end)
end
end)

# 645 "FStar.TypeChecker.Env.fst"
let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge Prims.option = (fun env l1 l2 -> if ((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid))) then begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end else begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end)

# 651 "FStar.TypeChecker.Env.fst"
let wp_sig_aux : FStar_Syntax_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun decls m -> (match ((FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))))) with
| None -> begin
(let _141_826 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _141_826))
end
| Some (md) -> begin
(
# 655 "FStar.TypeChecker.Env.fst"
let _52_973 = (inst_tscheme (md.FStar_Syntax_Syntax.univs, md.FStar_Syntax_Syntax.signature))
in (match (_52_973) with
| (_52_971, s) -> begin
(
# 656 "FStar.TypeChecker.Env.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match ((md.FStar_Syntax_Syntax.binders, s.FStar_Syntax_Syntax.n)) with
| ([], FStar_Syntax_Syntax.Tm_arrow ((a, _52_986)::(wp, _52_982)::(wlp, _52_978)::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _52_994 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))

# 661 "FStar.TypeChecker.Env.fst"
let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))

# 663 "FStar.TypeChecker.Env.fst"
let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_1001) -> begin
(
# 665 "FStar.TypeChecker.Env.fst"
let effects = (
# 665 "FStar.TypeChecker.Env.fst"
let _52_1004 = env.effects
in {decls = (ne)::env.effects.decls; order = _52_1004.order; joins = _52_1004.joins})
in (
# 666 "FStar.TypeChecker.Env.fst"
let _52_1007 = env
in {solver = _52_1007.solver; range = _52_1007.range; curmodule = _52_1007.curmodule; gamma = _52_1007.gamma; gamma_cache = _52_1007.gamma_cache; modules = _52_1007.modules; expected_typ = _52_1007.expected_typ; sigtab = _52_1007.sigtab; is_pattern = _52_1007.is_pattern; instantiate_imp = _52_1007.instantiate_imp; effects = effects; generalize = _52_1007.generalize; letrecs = _52_1007.letrecs; top_level = _52_1007.top_level; check_uvars = _52_1007.check_uvars; use_eq = _52_1007.use_eq; is_iface = _52_1007.is_iface; admit = _52_1007.admit; type_of = _52_1007.type_of; universe_of = _52_1007.universe_of; use_bv_sorts = _52_1007.use_bv_sorts}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _52_1011) -> begin
(
# 669 "FStar.TypeChecker.Env.fst"
let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _141_841 = (e1.mlift r wp1)
in (e2.mlift r _141_841)))})
in (
# 674 "FStar.TypeChecker.Env.fst"
let mk_lift = (fun lift_t r wp1 -> (
# 675 "FStar.TypeChecker.Env.fst"
let _52_1026 = (inst_tscheme lift_t)
in (match (_52_1026) with
| (_52_1024, lift_t) -> begin
(let _141_853 = (let _141_852 = (let _141_851 = (let _141_850 = (FStar_Syntax_Syntax.as_arg r)
in (let _141_849 = (let _141_848 = (FStar_Syntax_Syntax.as_arg wp1)
in (_141_848)::[])
in (_141_850)::_141_849))
in (lift_t, _141_851))
in FStar_Syntax_Syntax.Tm_app (_141_852))
in (FStar_Syntax_Syntax.mk _141_853 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (
# 678 "FStar.TypeChecker.Env.fst"
let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub.FStar_Syntax_Syntax.lift)}
in (
# 682 "FStar.TypeChecker.Env.fst"
let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (
# 687 "FStar.TypeChecker.Env.fst"
let print_mlift = (fun l -> (
# 688 "FStar.TypeChecker.Env.fst"
let arg = (let _141_870 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _141_870 FStar_Syntax_Syntax.Delta_constant None))
in (
# 689 "FStar.TypeChecker.Env.fst"
let wp = (let _141_871 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _141_871 FStar_Syntax_Syntax.Delta_constant None))
in (let _141_872 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _141_872)))))
in (
# 691 "FStar.TypeChecker.Env.fst"
let order = (edge)::env.effects.order
in (
# 693 "FStar.TypeChecker.Env.fst"
let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (
# 695 "FStar.TypeChecker.Env.fst"
let find_edge = (fun order _52_1043 -> (match (_52_1043) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _141_878 -> Some (_141_878)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (
# 704 "FStar.TypeChecker.Env.fst"
let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _141_886 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _141_885 = (find_edge order (i, k))
in (let _141_884 = (find_edge order (k, j))
in (_141_885, _141_884)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _52_1055 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _141_886))) order))
in (
# 715 "FStar.TypeChecker.Env.fst"
let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (
# 717 "FStar.TypeChecker.Env.fst"
let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (
# 720 "FStar.TypeChecker.Env.fst"
let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _141_978 = (find_edge order (i, k))
in (let _141_977 = (find_edge order (j, k))
in (_141_978, _141_977)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _52_1072, _52_1074) -> begin
if ((let _141_979 = (find_edge order (k, ub))
in (FStar_Util.is_some _141_979)) && (not ((let _141_980 = (find_edge order (ub, k))
in (FStar_Util.is_some _141_980))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _52_1078 -> begin
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
# 737 "FStar.TypeChecker.Env.fst"
let effects = (
# 737 "FStar.TypeChecker.Env.fst"
let _52_1087 = env.effects
in {decls = _52_1087.decls; order = order; joins = joins})
in (
# 740 "FStar.TypeChecker.Env.fst"
let _52_1090 = env
in {solver = _52_1090.solver; range = _52_1090.range; curmodule = _52_1090.curmodule; gamma = _52_1090.gamma; gamma_cache = _52_1090.gamma_cache; modules = _52_1090.modules; expected_typ = _52_1090.expected_typ; sigtab = _52_1090.sigtab; is_pattern = _52_1090.is_pattern; instantiate_imp = _52_1090.instantiate_imp; effects = effects; generalize = _52_1090.generalize; letrecs = _52_1090.letrecs; top_level = _52_1090.top_level; check_uvars = _52_1090.check_uvars; use_eq = _52_1090.use_eq; is_iface = _52_1090.is_iface; admit = _52_1090.admit; type_of = _52_1090.type_of; universe_of = _52_1090.universe_of; use_bv_sorts = _52_1090.use_bv_sorts})))))))))))))
end
| _52_1093 -> begin
env
end))

# 747 "FStar.TypeChecker.Env.fst"
let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (let _141_1029 = (
# 747 "FStar.TypeChecker.Env.fst"
let _52_1096 = env
in (let _141_1028 = (let _141_1027 = (let _141_1026 = (let _141_1025 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_141_1025, s))
in Binding_sig (_141_1026))
in (_141_1027)::env.gamma)
in {solver = _52_1096.solver; range = _52_1096.range; curmodule = _52_1096.curmodule; gamma = _141_1028; gamma_cache = _52_1096.gamma_cache; modules = _52_1096.modules; expected_typ = _52_1096.expected_typ; sigtab = _52_1096.sigtab; is_pattern = _52_1096.is_pattern; instantiate_imp = _52_1096.instantiate_imp; effects = _52_1096.effects; generalize = _52_1096.generalize; letrecs = _52_1096.letrecs; top_level = _52_1096.top_level; check_uvars = _52_1096.check_uvars; use_eq = _52_1096.use_eq; is_iface = _52_1096.is_iface; admit = _52_1096.admit; type_of = _52_1096.type_of; universe_of = _52_1096.universe_of; use_bv_sorts = _52_1096.use_bv_sorts}))
in (build_lattice _141_1029 s)))

# 749 "FStar.TypeChecker.Env.fst"
let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (let _141_1040 = (
# 749 "FStar.TypeChecker.Env.fst"
let _52_1101 = env
in (let _141_1039 = (let _141_1038 = (let _141_1037 = (let _141_1036 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_141_1036, s, us))
in Binding_sig_inst (_141_1037))
in (_141_1038)::env.gamma)
in {solver = _52_1101.solver; range = _52_1101.range; curmodule = _52_1101.curmodule; gamma = _141_1039; gamma_cache = _52_1101.gamma_cache; modules = _52_1101.modules; expected_typ = _52_1101.expected_typ; sigtab = _52_1101.sigtab; is_pattern = _52_1101.is_pattern; instantiate_imp = _52_1101.instantiate_imp; effects = _52_1101.effects; generalize = _52_1101.generalize; letrecs = _52_1101.letrecs; top_level = _52_1101.top_level; check_uvars = _52_1101.check_uvars; use_eq = _52_1101.use_eq; is_iface = _52_1101.is_iface; admit = _52_1101.admit; type_of = _52_1101.type_of; universe_of = _52_1101.universe_of; use_bv_sorts = _52_1101.use_bv_sorts}))
in (build_lattice _141_1040 s)))

# 751 "FStar.TypeChecker.Env.fst"
let push_local_binding : env  ->  binding  ->  env = (fun env b -> (
# 751 "FStar.TypeChecker.Env.fst"
let _52_1105 = env
in {solver = _52_1105.solver; range = _52_1105.range; curmodule = _52_1105.curmodule; gamma = (b)::env.gamma; gamma_cache = _52_1105.gamma_cache; modules = _52_1105.modules; expected_typ = _52_1105.expected_typ; sigtab = _52_1105.sigtab; is_pattern = _52_1105.is_pattern; instantiate_imp = _52_1105.instantiate_imp; effects = _52_1105.effects; generalize = _52_1105.generalize; letrecs = _52_1105.letrecs; top_level = _52_1105.top_level; check_uvars = _52_1105.check_uvars; use_eq = _52_1105.use_eq; is_iface = _52_1105.is_iface; admit = _52_1105.admit; type_of = _52_1105.type_of; universe_of = _52_1105.universe_of; use_bv_sorts = _52_1105.use_bv_sorts}))

# 753 "FStar.TypeChecker.Env.fst"
let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))

# 755 "FStar.TypeChecker.Env.fst"
let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _52_1115 -> (match (_52_1115) with
| (x, _52_1114) -> begin
(push_bv env x)
end)) env bs))

# 758 "FStar.TypeChecker.Env.fst"
let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(
# 760 "FStar.TypeChecker.Env.fst"
let _52_1120 = ()
in (
# 761 "FStar.TypeChecker.Env.fst"
let x = (
# 761 "FStar.TypeChecker.Env.fst"
let _52_1122 = x
in {FStar_Syntax_Syntax.ppname = _52_1122.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_1122.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, t))
end))

# 766 "FStar.TypeChecker.Env.fst"
let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))

# 768 "FStar.TypeChecker.Env.fst"
let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (
# 769 "FStar.TypeChecker.Env.fst"
let _52_1132 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (
# 770 "FStar.TypeChecker.Env.fst"
let _52_1134 = env
in {solver = _52_1134.solver; range = _52_1134.range; curmodule = _52_1134.curmodule; gamma = []; gamma_cache = _52_1134.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _52_1134.sigtab; is_pattern = _52_1134.is_pattern; instantiate_imp = _52_1134.instantiate_imp; effects = _52_1134.effects; generalize = _52_1134.generalize; letrecs = _52_1134.letrecs; top_level = _52_1134.top_level; check_uvars = _52_1134.check_uvars; use_eq = _52_1134.use_eq; is_iface = _52_1134.is_iface; admit = _52_1134.admit; type_of = _52_1134.type_of; universe_of = _52_1134.universe_of; use_bv_sorts = _52_1134.use_bv_sorts})))

# 775 "FStar.TypeChecker.Env.fst"
let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))

# 778 "FStar.TypeChecker.Env.fst"
let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (
# 779 "FStar.TypeChecker.Env.fst"
let _52_1142 = env
in {solver = _52_1142.solver; range = _52_1142.range; curmodule = _52_1142.curmodule; gamma = _52_1142.gamma; gamma_cache = _52_1142.gamma_cache; modules = _52_1142.modules; expected_typ = Some (t); sigtab = _52_1142.sigtab; is_pattern = _52_1142.is_pattern; instantiate_imp = _52_1142.instantiate_imp; effects = _52_1142.effects; generalize = _52_1142.generalize; letrecs = _52_1142.letrecs; top_level = _52_1142.top_level; check_uvars = _52_1142.check_uvars; use_eq = false; is_iface = _52_1142.is_iface; admit = _52_1142.admit; type_of = _52_1142.type_of; universe_of = _52_1142.universe_of; use_bv_sorts = _52_1142.use_bv_sorts}))

# 781 "FStar.TypeChecker.Env.fst"
let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

# 785 "FStar.TypeChecker.Env.fst"
let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _141_1083 = (expected_typ env)
in ((
# 786 "FStar.TypeChecker.Env.fst"
let _52_1149 = env
in {solver = _52_1149.solver; range = _52_1149.range; curmodule = _52_1149.curmodule; gamma = _52_1149.gamma; gamma_cache = _52_1149.gamma_cache; modules = _52_1149.modules; expected_typ = None; sigtab = _52_1149.sigtab; is_pattern = _52_1149.is_pattern; instantiate_imp = _52_1149.instantiate_imp; effects = _52_1149.effects; generalize = _52_1149.generalize; letrecs = _52_1149.letrecs; top_level = _52_1149.top_level; check_uvars = _52_1149.check_uvars; use_eq = false; is_iface = _52_1149.is_iface; admit = _52_1149.admit; type_of = _52_1149.type_of; universe_of = _52_1149.universe_of; use_bv_sorts = _52_1149.use_bv_sorts}), _141_1083)))

# 788 "FStar.TypeChecker.Env.fst"
let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (
# 789 "FStar.TypeChecker.Env.fst"
let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (
# 791 "FStar.TypeChecker.Env.fst"
let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(let _141_1089 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _52_12 -> (match (_52_12) with
| Binding_sig (_52_1156, se) -> begin
(se)::[]
end
| _52_1161 -> begin
[]
end))))
in (FStar_All.pipe_right _141_1089 FStar_List.rev))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (
# 797 "FStar.TypeChecker.Env.fst"
let _52_1163 = (add_sigelts env sigs)
in (
# 798 "FStar.TypeChecker.Env.fst"
let _52_1165 = env
in (let _141_1091 = (let _141_1090 = (gamma_cache env)
in (_141_1090)::[])
in {solver = _52_1165.solver; range = _52_1165.range; curmodule = empty_lid; gamma = []; gamma_cache = _141_1091; modules = (m)::env.modules; expected_typ = _52_1165.expected_typ; sigtab = _52_1165.sigtab; is_pattern = _52_1165.is_pattern; instantiate_imp = _52_1165.instantiate_imp; effects = _52_1165.effects; generalize = _52_1165.generalize; letrecs = _52_1165.letrecs; top_level = _52_1165.top_level; check_uvars = _52_1165.check_uvars; use_eq = _52_1165.use_eq; is_iface = _52_1165.is_iface; admit = _52_1165.admit; type_of = _52_1165.type_of; universe_of = _52_1165.universe_of; use_bv_sorts = _52_1165.use_bv_sorts}))))))

# 807 "FStar.TypeChecker.Env.fst"
let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (
# 808 "FStar.TypeChecker.Env.fst"
let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (
# 809 "FStar.TypeChecker.Env.fst"
let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (
# 810 "FStar.TypeChecker.Env.fst"
let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| Binding_univ (_52_1178)::tl -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _141_1103 = (let _141_1102 = (FStar_Syntax_Free.uvars t)
in (ext out _141_1102))
in (aux _141_1103 tl))
end
| (Binding_sig (_)::_) | (Binding_sig_inst (_)::_) -> begin
out
end))
in (aux no_uvs env.gamma)))))

# 819 "FStar.TypeChecker.Env.fst"
let univ_vars : env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun env -> (
# 820 "FStar.TypeChecker.Env.fst"
let no_univs = FStar_Syntax_Syntax.no_universe_uvars
in (
# 821 "FStar.TypeChecker.Env.fst"
let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (
# 822 "FStar.TypeChecker.Env.fst"
let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_sig_inst (_)::tl) | (Binding_univ (_)::tl) -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _141_1115 = (let _141_1114 = (FStar_Syntax_Free.univs t)
in (ext out _141_1114))
in (aux _141_1115 tl))
end
| Binding_sig (_52_1248)::_52_1246 -> begin
out
end))
in (aux no_univs env.gamma)))))

# 831 "FStar.TypeChecker.Env.fst"
let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _52_13 -> (match (_52_13) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))

# 839 "FStar.TypeChecker.Env.fst"
let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _141_1122 = (let _141_1121 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _141_1121 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _141_1122 FStar_List.rev)))

# 841 "FStar.TypeChecker.Env.fst"
let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))

# 843 "FStar.TypeChecker.Env.fst"
let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))

# 845 "FStar.TypeChecker.Env.fst"
let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))

# 847 "FStar.TypeChecker.Env.fst"
let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (
# 848 "FStar.TypeChecker.Env.fst"
let keys = (FStar_List.fold_left (fun keys _52_14 -> (match (_52_14) with
| Binding_sig (lids, _52_1280) -> begin
(FStar_List.append lids keys)
end
| _52_1284 -> begin
keys
end)) [] env.gamma)
in (let _141_1146 = (sigtab env)
in (FStar_Util.smap_fold _141_1146 (fun _52_1286 v keys -> (let _141_1145 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _141_1145 keys))) keys))))

# 855 "FStar.TypeChecker.Env.fst"
let dummy_solver : solver_t = {init = (fun _52_1290 -> ()); push = (fun _52_1292 -> ()); pop = (fun _52_1294 -> ()); mark = (fun _52_1296 -> ()); reset_mark = (fun _52_1298 -> ()); commit_mark = (fun _52_1300 -> ()); encode_modul = (fun _52_1302 _52_1304 -> ()); encode_sig = (fun _52_1306 _52_1308 -> ()); solve = (fun _52_1310 _52_1312 _52_1314 -> ()); is_trivial = (fun _52_1316 _52_1318 -> false); finish = (fun _52_1320 -> ()); refresh = (fun _52_1321 -> ())}

# 870 "FStar.TypeChecker.Env.fst"
let no_solver_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  env = (fun tc -> (let _141_1182 = (FStar_Ident.lid_of_path (("dummy")::[]) FStar_Range.dummyRange)
in (initial_env tc dummy_solver _141_1182)))




