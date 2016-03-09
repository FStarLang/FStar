
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
| Binding_var (_65_15) -> begin
_65_15
end))

# 32 "FStar.TypeChecker.Env.fst"
let ___Binding_lid____0 : binding  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme) = (fun projectee -> (match (projectee) with
| Binding_lid (_65_18) -> begin
_65_18
end))

# 33 "FStar.TypeChecker.Env.fst"
let ___Binding_sig____0 : binding  ->  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt) = (fun projectee -> (match (projectee) with
| Binding_sig (_65_21) -> begin
_65_21
end))

# 34 "FStar.TypeChecker.Env.fst"
let ___Binding_univ____0 : binding  ->  FStar_Syntax_Syntax.univ_name = (fun projectee -> (match (projectee) with
| Binding_univ (_65_24) -> begin
_65_24
end))

# 35 "FStar.TypeChecker.Env.fst"
let ___Binding_sig_inst____0 : binding  ->  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes) = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_65_27) -> begin
_65_27
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
let ___Unfold____0 : delta_level  ->  FStar_Syntax_Syntax.delta_depth = (fun projectee -> (match (projectee) with
| Unfold (_65_30) -> begin
_65_30
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

# 164 "FStar.TypeChecker.Env.fst"
let visible_at : delta_level  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun d q -> (match ((d, q)) with
| ((NoDelta, _)) | ((OnlyInline, FStar_Syntax_Syntax.Inline)) | ((Unfold (_), FStar_Syntax_Syntax.Inline)) | ((Unfold (_), FStar_Syntax_Syntax.Unfoldable)) -> begin
true
end
| _65_101 -> begin
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
let l = (match ((l1, l2)) with
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
end)
in Unfold (l))
end))

# 187 "FStar.TypeChecker.Env.fst"
let default_table_size : Prims.int = 200

# 188 "FStar.TypeChecker.Env.fst"
let new_sigtab = (fun _65_145 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))

# 190 "FStar.TypeChecker.Env.fst"
let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t))  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun tc solver module_lid -> (let _146_389 = (FStar_Util.smap_create 100)
in (let _146_388 = (let _146_385 = (new_sigtab ())
in (_146_385)::[])
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _146_389; modules = []; expected_typ = None; sigtab = _146_388; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []; type_of = tc; universe_of = (fun g e -> FStar_Syntax_Syntax.U_zero); use_bv_sorts = false})))

# 216 "FStar.TypeChecker.Env.fst"
let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> (FStar_List.hd env.sigtab))

# 217 "FStar.TypeChecker.Env.fst"
let push : env  ->  Prims.string  ->  env = (fun env msg -> (
# 218 "FStar.TypeChecker.Env.fst"
let _65_154 = (env.solver.push msg)
in (
# 219 "FStar.TypeChecker.Env.fst"
let _65_156 = env
in (let _146_398 = (let _146_397 = (let _146_396 = (sigtab env)
in (FStar_Util.smap_copy _146_396))
in (_146_397)::env.sigtab)
in {solver = _65_156.solver; range = _65_156.range; curmodule = _65_156.curmodule; gamma = _65_156.gamma; gamma_cache = _65_156.gamma_cache; modules = _65_156.modules; expected_typ = _65_156.expected_typ; sigtab = _146_398; is_pattern = _65_156.is_pattern; instantiate_imp = _65_156.instantiate_imp; effects = _65_156.effects; generalize = _65_156.generalize; letrecs = _65_156.letrecs; top_level = _65_156.top_level; check_uvars = _65_156.check_uvars; use_eq = _65_156.use_eq; is_iface = _65_156.is_iface; admit = _65_156.admit; default_effects = _65_156.default_effects; type_of = _65_156.type_of; universe_of = _65_156.universe_of; use_bv_sorts = _65_156.use_bv_sorts}))))

# 220 "FStar.TypeChecker.Env.fst"
let mark : env  ->  env = (fun env -> (
# 221 "FStar.TypeChecker.Env.fst"
let _65_159 = (env.solver.mark "USER MARK")
in (
# 222 "FStar.TypeChecker.Env.fst"
let _65_161 = env
in (let _146_403 = (let _146_402 = (let _146_401 = (sigtab env)
in (FStar_Util.smap_copy _146_401))
in (_146_402)::env.sigtab)
in {solver = _65_161.solver; range = _65_161.range; curmodule = _65_161.curmodule; gamma = _65_161.gamma; gamma_cache = _65_161.gamma_cache; modules = _65_161.modules; expected_typ = _65_161.expected_typ; sigtab = _146_403; is_pattern = _65_161.is_pattern; instantiate_imp = _65_161.instantiate_imp; effects = _65_161.effects; generalize = _65_161.generalize; letrecs = _65_161.letrecs; top_level = _65_161.top_level; check_uvars = _65_161.check_uvars; use_eq = _65_161.use_eq; is_iface = _65_161.is_iface; admit = _65_161.admit; default_effects = _65_161.default_effects; type_of = _65_161.type_of; universe_of = _65_161.universe_of; use_bv_sorts = _65_161.use_bv_sorts}))))

# 223 "FStar.TypeChecker.Env.fst"
let commit_mark : env  ->  env = (fun env -> (
# 224 "FStar.TypeChecker.Env.fst"
let _65_164 = (env.solver.commit_mark "USER MARK")
in (
# 225 "FStar.TypeChecker.Env.fst"
let sigtab = (match (env.sigtab) with
| hd::_65_168::tl -> begin
(hd)::tl
end
| _65_173 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 228 "FStar.TypeChecker.Env.fst"
let _65_175 = env
in {solver = _65_175.solver; range = _65_175.range; curmodule = _65_175.curmodule; gamma = _65_175.gamma; gamma_cache = _65_175.gamma_cache; modules = _65_175.modules; expected_typ = _65_175.expected_typ; sigtab = sigtab; is_pattern = _65_175.is_pattern; instantiate_imp = _65_175.instantiate_imp; effects = _65_175.effects; generalize = _65_175.generalize; letrecs = _65_175.letrecs; top_level = _65_175.top_level; check_uvars = _65_175.check_uvars; use_eq = _65_175.use_eq; is_iface = _65_175.is_iface; admit = _65_175.admit; default_effects = _65_175.default_effects; type_of = _65_175.type_of; universe_of = _65_175.universe_of; use_bv_sorts = _65_175.use_bv_sorts}))))

# 229 "FStar.TypeChecker.Env.fst"
let reset_mark : env  ->  env = (fun env -> (
# 230 "FStar.TypeChecker.Env.fst"
let _65_178 = (env.solver.reset_mark "USER MARK")
in (
# 231 "FStar.TypeChecker.Env.fst"
let _65_180 = env
in (let _146_408 = (FStar_List.tl env.sigtab)
in {solver = _65_180.solver; range = _65_180.range; curmodule = _65_180.curmodule; gamma = _65_180.gamma; gamma_cache = _65_180.gamma_cache; modules = _65_180.modules; expected_typ = _65_180.expected_typ; sigtab = _146_408; is_pattern = _65_180.is_pattern; instantiate_imp = _65_180.instantiate_imp; effects = _65_180.effects; generalize = _65_180.generalize; letrecs = _65_180.letrecs; top_level = _65_180.top_level; check_uvars = _65_180.check_uvars; use_eq = _65_180.use_eq; is_iface = _65_180.is_iface; admit = _65_180.admit; default_effects = _65_180.default_effects; type_of = _65_180.type_of; universe_of = _65_180.universe_of; use_bv_sorts = _65_180.use_bv_sorts}))))

# 232 "FStar.TypeChecker.Env.fst"
let pop : env  ->  Prims.string  ->  env = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(FStar_All.failwith "Too many pops")
end
| _65_190::tl -> begin
(
# 236 "FStar.TypeChecker.Env.fst"
let _65_192 = (env.solver.pop msg)
in (
# 237 "FStar.TypeChecker.Env.fst"
let _65_194 = env
in {solver = _65_194.solver; range = _65_194.range; curmodule = _65_194.curmodule; gamma = _65_194.gamma; gamma_cache = _65_194.gamma_cache; modules = _65_194.modules; expected_typ = _65_194.expected_typ; sigtab = tl; is_pattern = _65_194.is_pattern; instantiate_imp = _65_194.instantiate_imp; effects = _65_194.effects; generalize = _65_194.generalize; letrecs = _65_194.letrecs; top_level = _65_194.top_level; check_uvars = _65_194.check_uvars; use_eq = _65_194.use_eq; is_iface = _65_194.is_iface; admit = _65_194.admit; default_effects = _65_194.default_effects; type_of = _65_194.type_of; universe_of = _65_194.universe_of; use_bv_sorts = _65_194.use_bv_sorts}))
end))

# 242 "FStar.TypeChecker.Env.fst"
let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> ((let _146_418 = (FStar_ST.read FStar_Options.debug)
in (FStar_All.pipe_right _146_418 (FStar_Util.for_some (fun x -> ((env.curmodule.FStar_Ident.str = "") || (env.curmodule.FStar_Ident.str = x)))))) && (FStar_Options.debug_level_geq l)))

# 245 "FStar.TypeChecker.Env.fst"
let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(
# 245 "FStar.TypeChecker.Env.fst"
let _65_201 = e
in {solver = _65_201.solver; range = r; curmodule = _65_201.curmodule; gamma = _65_201.gamma; gamma_cache = _65_201.gamma_cache; modules = _65_201.modules; expected_typ = _65_201.expected_typ; sigtab = _65_201.sigtab; is_pattern = _65_201.is_pattern; instantiate_imp = _65_201.instantiate_imp; effects = _65_201.effects; generalize = _65_201.generalize; letrecs = _65_201.letrecs; top_level = _65_201.top_level; check_uvars = _65_201.check_uvars; use_eq = _65_201.use_eq; is_iface = _65_201.is_iface; admit = _65_201.admit; default_effects = _65_201.default_effects; type_of = _65_201.type_of; universe_of = _65_201.universe_of; use_bv_sorts = _65_201.use_bv_sorts})
end)

# 246 "FStar.TypeChecker.Env.fst"
let get_range : env  ->  FStar_Range.range = (fun e -> e.range)

# 251 "FStar.TypeChecker.Env.fst"
let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)

# 252 "FStar.TypeChecker.Env.fst"
let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)

# 253 "FStar.TypeChecker.Env.fst"
let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (
# 253 "FStar.TypeChecker.Env.fst"
let _65_208 = env
in {solver = _65_208.solver; range = _65_208.range; curmodule = lid; gamma = _65_208.gamma; gamma_cache = _65_208.gamma_cache; modules = _65_208.modules; expected_typ = _65_208.expected_typ; sigtab = _65_208.sigtab; is_pattern = _65_208.is_pattern; instantiate_imp = _65_208.instantiate_imp; effects = _65_208.effects; generalize = _65_208.generalize; letrecs = _65_208.letrecs; top_level = _65_208.top_level; check_uvars = _65_208.check_uvars; use_eq = _65_208.use_eq; is_iface = _65_208.is_iface; admit = _65_208.admit; default_effects = _65_208.default_effects; type_of = _65_208.type_of; universe_of = _65_208.universe_of; use_bv_sorts = _65_208.use_bv_sorts}))

# 254 "FStar.TypeChecker.Env.fst"
let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))

# 255 "FStar.TypeChecker.Env.fst"
let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (let _146_442 = (sigtab env)
in (FStar_Util.smap_try_find _146_442 (FStar_Ident.text_of_lid lid))))

# 257 "FStar.TypeChecker.Env.fst"
let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))

# 260 "FStar.TypeChecker.Env.fst"
let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _146_447 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _146_447)))

# 264 "FStar.TypeChecker.Env.fst"
let new_u_univ = (fun _65_217 -> (let _146_449 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_146_449)))

# 267 "FStar.TypeChecker.Env.fst"
let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match ((ts, us)) with
| (([], t), []) -> begin
([], t)
end
| ((formals, t), _65_230) -> begin
(
# 271 "FStar.TypeChecker.Env.fst"
let _65_232 = ()
in (
# 272 "FStar.TypeChecker.Env.fst"
let n = ((FStar_List.length formals) - 1)
in (
# 273 "FStar.TypeChecker.Env.fst"
let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN (((n - i), u)))))
in (let _146_456 = (FStar_Syntax_Subst.subst vs t)
in (us, _146_456)))))
end))

# 277 "FStar.TypeChecker.Env.fst"
let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _65_1 -> (match (_65_1) with
| ([], t) -> begin
([], t)
end
| (us, t) -> begin
(
# 280 "FStar.TypeChecker.Env.fst"
let us' = (FStar_All.pipe_right us (FStar_List.map (fun _65_245 -> (new_u_univ ()))))
in (inst_tscheme_with (us, t) us'))
end))

# 283 "FStar.TypeChecker.Env.fst"
let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed _65_253 -> (match (_65_253) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(
# 286 "FStar.TypeChecker.Env.fst"
let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in (
# 287 "FStar.TypeChecker.Env.fst"
let _65_256 = if ((FStar_List.length insts) <> (FStar_List.length univs)) then begin
(let _146_472 = (let _146_471 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _146_470 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _146_469 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _146_468 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _146_471 _146_470 _146_469 _146_468)))))
in (FStar_All.failwith _146_472))
end else begin
()
end
in (let _146_473 = (inst_tscheme_with ((FStar_List.append ed.FStar_Syntax_Syntax.univs us), t) insts)
in (Prims.snd _146_473))))
end
| _65_259 -> begin
(let _146_475 = (let _146_474 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _146_474))
in (FStar_All.failwith _146_475))
end)
end))

# 294 "FStar.TypeChecker.Env.fst"
type tri =
| Yes
| No
| Maybe

# 295 "FStar.TypeChecker.Env.fst"
let is_Yes = (fun _discr_ -> (match (_discr_) with
| Yes (_) -> begin
true
end
| _ -> begin
false
end))

# 296 "FStar.TypeChecker.Env.fst"
let is_No = (fun _discr_ -> (match (_discr_) with
| No (_) -> begin
true
end
| _ -> begin
false
end))

# 297 "FStar.TypeChecker.Env.fst"
let is_Maybe = (fun _discr_ -> (match (_discr_) with
| Maybe (_) -> begin
true
end
| _ -> begin
false
end))

# 299 "FStar.TypeChecker.Env.fst"
let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (
# 300 "FStar.TypeChecker.Env.fst"
let cur = (current_module env)
in if (l.FStar_Ident.nsstr = cur.FStar_Ident.str) then begin
Yes
end else begin
if (FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str) then begin
(
# 303 "FStar.TypeChecker.Env.fst"
let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (
# 304 "FStar.TypeChecker.Env.fst"
let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (
# 305 "FStar.TypeChecker.Env.fst"
let rec aux = (fun c l -> (match ((c, l)) with
| ([], _65_270) -> begin
Maybe
end
| (_65_273, []) -> begin
No
end
| (hd::tl, hd'::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _65_284 -> begin
No
end))
in (aux cur lns))))
end else begin
No
end
end))

# 313 "FStar.TypeChecker.Env.fst"
let lookup_qname : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either Prims.option = (fun env lid -> (
# 314 "FStar.TypeChecker.Env.fst"
let cur_mod = (in_cur_mod env lid)
in (
# 315 "FStar.TypeChecker.Env.fst"
let cache = (fun t -> (
# 315 "FStar.TypeChecker.Env.fst"
let _65_290 = (FStar_Util.smap_add env.gamma_cache lid.FStar_Ident.str t)
in Some (t)))
in (
# 316 "FStar.TypeChecker.Env.fst"
let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find env.gamma_cache lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _65_2 -> (match (_65_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _146_495 = (let _146_494 = (inst_tscheme t)
in FStar_Util.Inl (_146_494))
in Some (_146_495))
end else begin
None
end
end
| Binding_sig (_65_299, FStar_Syntax_Syntax.Sig_bundle (ses, _65_302, _65_304, _65_306)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _146_497 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _146_497 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr ((se, None))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(
# 327 "FStar.TypeChecker.Env.fst"
let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_65_319) -> begin
Some (t)
end
| _65_322 -> begin
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
| _65_329 -> begin
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

# 344 "FStar.TypeChecker.Env.fst"
let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| None -> begin
false
end
| Some (_65_339) -> begin
true
end))

# 348 "FStar.TypeChecker.Env.fst"
let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _65_345, _65_347, _65_349) -> begin
(add_sigelts env ses)
end
| _65_353 -> begin
(
# 351 "FStar.TypeChecker.Env.fst"
let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _146_511 = (sigtab env)
in (FStar_Util.smap_add _146_511 l.FStar_Ident.str se))) lids))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))

# 360 "FStar.TypeChecker.Env.fst"
let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun _65_3 -> (match (_65_3) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _65_364 -> begin
None
end))))

# 366 "FStar.TypeChecker.Env.fst"
let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _65_4 -> (match (_65_4) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _65_371 -> begin
false
end)) env.gamma) FStar_Option.isSome))

# 372 "FStar.TypeChecker.Env.fst"
let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_65_375, lb::[]), _65_380, _65_382, _65_384) -> begin
(let _146_531 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_146_531))
end
| FStar_Syntax_Syntax.Sig_let ((_65_388, lbs), _65_392, _65_394, _65_396) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_65_401) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _146_533 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_146_533))
end else begin
None
end
end)))
end
| _65_406 -> begin
None
end))

# 386 "FStar.TypeChecker.Env.fst"
let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _146_541 = (let _146_540 = (let _146_539 = (variable_not_found bv)
in (let _146_538 = (FStar_Syntax_Syntax.range_of_bv bv)
in (_146_539, _146_538)))
in FStar_Syntax_Syntax.Error (_146_540))
in (Prims.raise _146_541))
end
| Some (t) -> begin
t
end))

# 391 "FStar.TypeChecker.Env.fst"
let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _65_415) -> begin
(let _146_547 = (let _146_546 = (let _146_545 = (let _146_544 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _146_544))
in (ne.FStar_Syntax_Syntax.univs, _146_545))
in (inst_tscheme _146_546))
in Some (_146_547))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _65_422, _65_424, _65_426) -> begin
(let _146_551 = (let _146_550 = (let _146_549 = (let _146_548 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _146_548))
in (us, _146_549))
in (inst_tscheme _146_550))
in Some (_146_551))
end
| _65_430 -> begin
None
end))

# 401 "FStar.TypeChecker.Env.fst"
let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_65_440, t) -> begin
Some (t)
end)
end
| _65_445 -> begin
None
end))

# 410 "FStar.TypeChecker.Env.fst"
let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env lid -> (
# 411 "FStar.TypeChecker.Env.fst"
let mapper = (fun _65_5 -> (match (_65_5) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_65_452, uvs, t, _65_456, _65_458, _65_460, _65_462, _65_464), None) -> begin
(let _146_562 = (inst_tscheme (uvs, t))
in Some (_146_562))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _65_475), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _146_563 = (inst_tscheme (uvs, t))
in Some (_146_563))
end else begin
None
end
end else begin
(let _146_564 = (inst_tscheme (uvs, t))
in Some (_146_564))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _65_486, _65_488, _65_490, _65_492), None) -> begin
(match (tps) with
| [] -> begin
(let _146_566 = (inst_tscheme (uvs, k))
in (FStar_All.pipe_left (fun _146_565 -> Some (_146_565)) _146_566))
end
| _65_500 -> begin
(let _146_571 = (let _146_570 = (let _146_569 = (let _146_568 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _146_568))
in (uvs, _146_569))
in (inst_tscheme _146_570))
in (FStar_All.pipe_left (fun _146_567 -> Some (_146_567)) _146_571))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _65_506, _65_508, _65_510, _65_512), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _146_573 = (inst_tscheme_with (uvs, k) us)
in (FStar_All.pipe_left (fun _146_572 -> Some (_146_572)) _146_573))
end
| _65_521 -> begin
(let _146_578 = (let _146_577 = (let _146_576 = (let _146_575 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _146_575))
in (uvs, _146_576))
in (inst_tscheme_with _146_577 us))
in (FStar_All.pipe_left (fun _146_574 -> Some (_146_574)) _146_578))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_65_525), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _65_530 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _146_579 = (lookup_qname env lid)
in (FStar_Util.bind_opt _146_579 mapper))) with
| Some (us, t) -> begin
Some ((us, (
# 445 "FStar.TypeChecker.Env.fst"
let _65_536 = t
in {FStar_Syntax_Syntax.n = _65_536.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _65_536.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _65_536.FStar_Syntax_Syntax.vars})))
end
| None -> begin
None
end)))

# 448 "FStar.TypeChecker.Env.fst"
let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _146_586 = (let _146_585 = (let _146_584 = (name_not_found l)
in (_146_584, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_146_585))
in (Prims.raise _146_586))
end
| Some (x) -> begin
x
end))

# 453 "FStar.TypeChecker.Env.fst"
let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_65_547, uvs, t, _65_551, _65_553), None)) -> begin
(inst_tscheme (uvs, t))
end
| _65_561 -> begin
(let _146_593 = (let _146_592 = (let _146_591 = (name_not_found lid)
in (_146_591, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_146_592))
in (Prims.raise _146_593))
end))

# 458 "FStar.TypeChecker.Env.fst"
let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_65_565, uvs, t, _65_569, _65_571, _65_573, _65_575, _65_577), None)) -> begin
(inst_tscheme (uvs, t))
end
| _65_585 -> begin
(let _146_600 = (let _146_599 = (let _146_598 = (name_not_found lid)
in (_146_598, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_146_599))
in (Prims.raise _146_600))
end))

# 463 "FStar.TypeChecker.Env.fst"
let lookup_definition : delta_level  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_65_595, lbs), _65_599, _65_601, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (
# 469 "FStar.TypeChecker.Env.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _146_609 = (let _146_608 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (lb.FStar_Syntax_Syntax.lbunivs, _146_608))
in Some (_146_609))
end else begin
None
end)))
end
| _65_608 -> begin
None
end)
end
| _65_610 -> begin
None
end))

# 477 "FStar.TypeChecker.Env.fst"
let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _146_616 = (let _146_615 = (let _146_614 = (name_not_found ftv)
in (_146_614, (FStar_Ident.range_of_lid ftv)))
in FStar_Syntax_Syntax.Error (_146_615))
in (Prims.raise _146_616))
end
| Some (k) -> begin
k
end))

# 482 "FStar.TypeChecker.Env.fst"
let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (
# 483 "FStar.TypeChecker.Env.fst"
let fail = (fun _65_620 -> (match (()) with
| () -> begin
(let _146_627 = (let _146_626 = (FStar_Util.string_of_int i)
in (let _146_625 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _146_626 _146_625)))
in (FStar_All.failwith _146_627))
end))
in (
# 484 "FStar.TypeChecker.Env.fst"
let _65_624 = (lookup_datacon env lid)
in (match (_65_624) with
| (_65_622, t) -> begin
(match ((let _146_628 = (FStar_Syntax_Subst.compress t)
in _146_628.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _65_627) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(
# 489 "FStar.TypeChecker.Env.fst"
let b = (FStar_List.nth binders i)
in (let _146_629 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _146_629 Prims.fst)))
end
end
| _65_632 -> begin
(fail ())
end)
end))))

# 493 "FStar.TypeChecker.Env.fst"
let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_65_636, uvs, t, q, _65_641), None)) -> begin
Some (((uvs, t), q))
end
| _65_649 -> begin
None
end))

# 498 "FStar.TypeChecker.Env.fst"
let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _65_659), None)) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _65_6 -> (match (_65_6) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _65_669 -> begin
false
end)))) then begin
None
end else begin
(
# 503 "FStar.TypeChecker.Env.fst"
let insts = if (FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid) then begin
(univ)::(FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]
end else begin
(univ)::[]
end
in (match ((binders, univs)) with
| ([], _65_673) -> begin
(FStar_All.failwith "Unexpected effect abbreviation with no arguments")
end
| (_65_676, _65_683::_65_680::_65_678) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(let _146_643 = (let _146_642 = (FStar_Syntax_Print.lid_to_string lid)
in (let _146_641 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _146_642 _146_641)))
in (FStar_All.failwith _146_643))
end
| _65_687 -> begin
(
# 511 "FStar.TypeChecker.Env.fst"
let _65_691 = (let _146_645 = (let _146_644 = (FStar_Syntax_Util.arrow binders c)
in (univs, _146_644))
in (inst_tscheme_with _146_645 insts))
in (match (_65_691) with
| (_65_689, t) -> begin
(match ((let _146_646 = (FStar_Syntax_Subst.compress t)
in _146_646.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some ((binders, c))
end
| _65_697 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end))
end
end
| _65_699 -> begin
None
end))

# 520 "FStar.TypeChecker.Env.fst"
let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_65_703, _65_705, _65_707, _65_709, _65_711, dcs, _65_714, _65_716), _65_720)) -> begin
dcs
end
| _65_725 -> begin
[]
end))

# 525 "FStar.TypeChecker.Env.fst"
let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_65_729, _65_731, _65_733, l, _65_736, _65_738, _65_740, _65_742), _65_746)) -> begin
l
end
| _65_751 -> begin
(let _146_656 = (let _146_655 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _146_655))
in (FStar_All.failwith _146_656))
end))

# 530 "FStar.TypeChecker.Env.fst"
let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_65_755, _65_757, _65_759, _65_761, _65_763, _65_765, _65_767, _65_769), _65_773)) -> begin
true
end
| _65_778 -> begin
false
end))

# 535 "FStar.TypeChecker.Env.fst"
let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_65_782, _65_784, _65_786, _65_788, _65_790, _65_792, tags, _65_795), _65_799)) -> begin
(FStar_Util.for_some (fun _65_7 -> (match (_65_7) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _65_811 -> begin
false
end)) tags)
end
| _65_813 -> begin
false
end))

# 541 "FStar.TypeChecker.Env.fst"
let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_65_817, _65_819, _65_821, quals, _65_824), _65_828)) -> begin
(FStar_Util.for_some (fun _65_8 -> (match (_65_8) with
| FStar_Syntax_Syntax.Projector (_65_834) -> begin
true
end
| _65_837 -> begin
false
end)) quals)
end
| _65_839 -> begin
false
end))

# 547 "FStar.TypeChecker.Env.fst"
let interpreted_symbols : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]

# 564 "FStar.TypeChecker.Env.fst"
let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env head -> (match ((let _146_675 = (FStar_Syntax_Util.un_uinst head)
in _146_675.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _65_845 -> begin
false
end))

# 574 "FStar.TypeChecker.Env.fst"
let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))

# 577 "FStar.TypeChecker.Env.fst"
let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _146_687 = (let _146_686 = (let _146_685 = (name_not_found l)
in (_146_685, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_146_686))
in (Prims.raise _146_687))
end
| Some (md) -> begin
md
end))

# 582 "FStar.TypeChecker.Env.fst"
let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
(l1, (fun t wp -> wp), (fun t wp -> wp))
end else begin
if (((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid))) then begin
(FStar_Syntax_Const.effect_GTot_lid, (fun t wp -> wp), (fun t wp -> wp))
end else begin
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _65_873 -> (match (_65_873) with
| (m1, m2, _65_868, _65_870, _65_872) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _146_763 = (let _146_762 = (let _146_761 = (let _146_760 = (FStar_Syntax_Print.lid_to_string l1)
in (let _146_759 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _146_760 _146_759)))
in (_146_761, env.range))
in FStar_Syntax_Syntax.Error (_146_762))
in (Prims.raise _146_763))
end
| Some (_65_876, _65_878, m3, j1, j2) -> begin
(m3, j1, j2)
end)
end
end)

# 592 "FStar.TypeChecker.Env.fst"
let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge Prims.option = (fun env l1 l2 -> if ((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid))) then begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end else begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end)

# 598 "FStar.TypeChecker.Env.fst"
let wp_sig_aux : FStar_Syntax_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun decls m -> (match ((FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))))) with
| None -> begin
(let _146_778 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _146_778))
end
| Some (md) -> begin
(
# 602 "FStar.TypeChecker.Env.fst"
let _65_899 = (inst_tscheme (md.FStar_Syntax_Syntax.univs, md.FStar_Syntax_Syntax.signature))
in (match (_65_899) with
| (_65_897, s) -> begin
(
# 603 "FStar.TypeChecker.Env.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match ((md.FStar_Syntax_Syntax.binders, s.FStar_Syntax_Syntax.n)) with
| ([], FStar_Syntax_Syntax.Tm_arrow ((a, _65_912)::(wp, _65_908)::(wlp, _65_904)::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _65_920 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))

# 608 "FStar.TypeChecker.Env.fst"
let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))

# 610 "FStar.TypeChecker.Env.fst"
let default_effect : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (FStar_Util.find_map env.default_effects (fun _65_927 -> (match (_65_927) with
| (l', m) -> begin
if (FStar_Ident.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))

# 612 "FStar.TypeChecker.Env.fst"
let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, _65_932, _65_934, c, quals, r) -> begin
(match ((FStar_Util.find_map quals (fun _65_9 -> (match (_65_9) with
| FStar_Syntax_Syntax.DefaultEffect (n) -> begin
n
end
| _65_944 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(
# 616 "FStar.TypeChecker.Env.fst"
let _65_948 = env
in {solver = _65_948.solver; range = _65_948.range; curmodule = _65_948.curmodule; gamma = _65_948.gamma; gamma_cache = _65_948.gamma_cache; modules = _65_948.modules; expected_typ = _65_948.expected_typ; sigtab = _65_948.sigtab; is_pattern = _65_948.is_pattern; instantiate_imp = _65_948.instantiate_imp; effects = _65_948.effects; generalize = _65_948.generalize; letrecs = _65_948.letrecs; top_level = _65_948.top_level; check_uvars = _65_948.check_uvars; use_eq = _65_948.use_eq; is_iface = _65_948.is_iface; admit = _65_948.admit; default_effects = ((e, l))::env.default_effects; type_of = _65_948.type_of; universe_of = _65_948.universe_of; use_bv_sorts = _65_948.use_bv_sorts})
end)
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _65_952) -> begin
(
# 619 "FStar.TypeChecker.Env.fst"
let effects = (
# 619 "FStar.TypeChecker.Env.fst"
let _65_955 = env.effects
in {decls = (ne)::env.effects.decls; order = _65_955.order; joins = _65_955.joins})
in (
# 620 "FStar.TypeChecker.Env.fst"
let _65_958 = env
in {solver = _65_958.solver; range = _65_958.range; curmodule = _65_958.curmodule; gamma = _65_958.gamma; gamma_cache = _65_958.gamma_cache; modules = _65_958.modules; expected_typ = _65_958.expected_typ; sigtab = _65_958.sigtab; is_pattern = _65_958.is_pattern; instantiate_imp = _65_958.instantiate_imp; effects = effects; generalize = _65_958.generalize; letrecs = _65_958.letrecs; top_level = _65_958.top_level; check_uvars = _65_958.check_uvars; use_eq = _65_958.use_eq; is_iface = _65_958.is_iface; admit = _65_958.admit; default_effects = _65_958.default_effects; type_of = _65_958.type_of; universe_of = _65_958.universe_of; use_bv_sorts = _65_958.use_bv_sorts}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _65_962) -> begin
(
# 623 "FStar.TypeChecker.Env.fst"
let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _146_799 = (e1.mlift r wp1)
in (e2.mlift r _146_799)))})
in (
# 628 "FStar.TypeChecker.Env.fst"
let mk_lift = (fun lift_t r wp1 -> (
# 629 "FStar.TypeChecker.Env.fst"
let _65_977 = (inst_tscheme lift_t)
in (match (_65_977) with
| (_65_975, lift_t) -> begin
(let _146_811 = (let _146_810 = (let _146_809 = (let _146_808 = (FStar_Syntax_Syntax.as_arg r)
in (let _146_807 = (let _146_806 = (FStar_Syntax_Syntax.as_arg wp1)
in (_146_806)::[])
in (_146_808)::_146_807))
in (lift_t, _146_809))
in FStar_Syntax_Syntax.Tm_app (_146_810))
in (FStar_Syntax_Syntax.mk _146_811 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (
# 632 "FStar.TypeChecker.Env.fst"
let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub.FStar_Syntax_Syntax.lift)}
in (
# 636 "FStar.TypeChecker.Env.fst"
let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (
# 641 "FStar.TypeChecker.Env.fst"
let print_mlift = (fun l -> (
# 642 "FStar.TypeChecker.Env.fst"
let arg = (let _146_828 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _146_828 FStar_Syntax_Syntax.Delta_constant None))
in (
# 643 "FStar.TypeChecker.Env.fst"
let wp = (let _146_829 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _146_829 FStar_Syntax_Syntax.Delta_constant None))
in (let _146_830 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _146_830)))))
in (
# 645 "FStar.TypeChecker.Env.fst"
let order = (edge)::env.effects.order
in (
# 647 "FStar.TypeChecker.Env.fst"
let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (
# 649 "FStar.TypeChecker.Env.fst"
let find_edge = (fun order _65_994 -> (match (_65_994) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _146_836 -> Some (_146_836)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (
# 658 "FStar.TypeChecker.Env.fst"
let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _146_844 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _146_843 = (find_edge order (i, k))
in (let _146_842 = (find_edge order (k, j))
in (_146_843, _146_842)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _65_1006 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _146_844))) order))
in (
# 669 "FStar.TypeChecker.Env.fst"
let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (
# 671 "FStar.TypeChecker.Env.fst"
let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (
# 674 "FStar.TypeChecker.Env.fst"
let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _146_936 = (find_edge order (i, k))
in (let _146_935 = (find_edge order (j, k))
in (_146_936, _146_935)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _65_1023, _65_1025) -> begin
if ((let _146_937 = (find_edge order (k, ub))
in (FStar_Util.is_some _146_937)) && (not ((let _146_938 = (find_edge order (ub, k))
in (FStar_Util.is_some _146_938))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _65_1029 -> begin
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
# 691 "FStar.TypeChecker.Env.fst"
let effects = (
# 691 "FStar.TypeChecker.Env.fst"
let _65_1038 = env.effects
in {decls = _65_1038.decls; order = order; joins = joins})
in (
# 694 "FStar.TypeChecker.Env.fst"
let _65_1041 = env
in {solver = _65_1041.solver; range = _65_1041.range; curmodule = _65_1041.curmodule; gamma = _65_1041.gamma; gamma_cache = _65_1041.gamma_cache; modules = _65_1041.modules; expected_typ = _65_1041.expected_typ; sigtab = _65_1041.sigtab; is_pattern = _65_1041.is_pattern; instantiate_imp = _65_1041.instantiate_imp; effects = effects; generalize = _65_1041.generalize; letrecs = _65_1041.letrecs; top_level = _65_1041.top_level; check_uvars = _65_1041.check_uvars; use_eq = _65_1041.use_eq; is_iface = _65_1041.is_iface; admit = _65_1041.admit; default_effects = _65_1041.default_effects; type_of = _65_1041.type_of; universe_of = _65_1041.universe_of; use_bv_sorts = _65_1041.use_bv_sorts})))))))))))))
end
| _65_1044 -> begin
env
end))

# 701 "FStar.TypeChecker.Env.fst"
let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (let _146_987 = (
# 701 "FStar.TypeChecker.Env.fst"
let _65_1047 = env
in (let _146_986 = (let _146_985 = (let _146_984 = (let _146_983 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_146_983, s))
in Binding_sig (_146_984))
in (_146_985)::env.gamma)
in {solver = _65_1047.solver; range = _65_1047.range; curmodule = _65_1047.curmodule; gamma = _146_986; gamma_cache = _65_1047.gamma_cache; modules = _65_1047.modules; expected_typ = _65_1047.expected_typ; sigtab = _65_1047.sigtab; is_pattern = _65_1047.is_pattern; instantiate_imp = _65_1047.instantiate_imp; effects = _65_1047.effects; generalize = _65_1047.generalize; letrecs = _65_1047.letrecs; top_level = _65_1047.top_level; check_uvars = _65_1047.check_uvars; use_eq = _65_1047.use_eq; is_iface = _65_1047.is_iface; admit = _65_1047.admit; default_effects = _65_1047.default_effects; type_of = _65_1047.type_of; universe_of = _65_1047.universe_of; use_bv_sorts = _65_1047.use_bv_sorts}))
in (build_lattice _146_987 s)))

# 703 "FStar.TypeChecker.Env.fst"
let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (let _146_998 = (
# 703 "FStar.TypeChecker.Env.fst"
let _65_1052 = env
in (let _146_997 = (let _146_996 = (let _146_995 = (let _146_994 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_146_994, s, us))
in Binding_sig_inst (_146_995))
in (_146_996)::env.gamma)
in {solver = _65_1052.solver; range = _65_1052.range; curmodule = _65_1052.curmodule; gamma = _146_997; gamma_cache = _65_1052.gamma_cache; modules = _65_1052.modules; expected_typ = _65_1052.expected_typ; sigtab = _65_1052.sigtab; is_pattern = _65_1052.is_pattern; instantiate_imp = _65_1052.instantiate_imp; effects = _65_1052.effects; generalize = _65_1052.generalize; letrecs = _65_1052.letrecs; top_level = _65_1052.top_level; check_uvars = _65_1052.check_uvars; use_eq = _65_1052.use_eq; is_iface = _65_1052.is_iface; admit = _65_1052.admit; default_effects = _65_1052.default_effects; type_of = _65_1052.type_of; universe_of = _65_1052.universe_of; use_bv_sorts = _65_1052.use_bv_sorts}))
in (build_lattice _146_998 s)))

# 705 "FStar.TypeChecker.Env.fst"
let push_local_binding : env  ->  binding  ->  env = (fun env b -> (
# 705 "FStar.TypeChecker.Env.fst"
let _65_1056 = env
in {solver = _65_1056.solver; range = _65_1056.range; curmodule = _65_1056.curmodule; gamma = (b)::env.gamma; gamma_cache = _65_1056.gamma_cache; modules = _65_1056.modules; expected_typ = _65_1056.expected_typ; sigtab = _65_1056.sigtab; is_pattern = _65_1056.is_pattern; instantiate_imp = _65_1056.instantiate_imp; effects = _65_1056.effects; generalize = _65_1056.generalize; letrecs = _65_1056.letrecs; top_level = _65_1056.top_level; check_uvars = _65_1056.check_uvars; use_eq = _65_1056.use_eq; is_iface = _65_1056.is_iface; admit = _65_1056.admit; default_effects = _65_1056.default_effects; type_of = _65_1056.type_of; universe_of = _65_1056.universe_of; use_bv_sorts = _65_1056.use_bv_sorts}))

# 707 "FStar.TypeChecker.Env.fst"
let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))

# 709 "FStar.TypeChecker.Env.fst"
let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _65_1066 -> (match (_65_1066) with
| (x, _65_1065) -> begin
(push_bv env x)
end)) env bs))

# 712 "FStar.TypeChecker.Env.fst"
let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(
# 714 "FStar.TypeChecker.Env.fst"
let _65_1071 = ()
in (
# 715 "FStar.TypeChecker.Env.fst"
let x = (
# 715 "FStar.TypeChecker.Env.fst"
let _65_1073 = x
in {FStar_Syntax_Syntax.ppname = _65_1073.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_1073.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, t))
end))

# 720 "FStar.TypeChecker.Env.fst"
let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))

# 722 "FStar.TypeChecker.Env.fst"
let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (
# 723 "FStar.TypeChecker.Env.fst"
let _65_1083 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (
# 724 "FStar.TypeChecker.Env.fst"
let _65_1085 = env
in {solver = _65_1085.solver; range = _65_1085.range; curmodule = _65_1085.curmodule; gamma = []; gamma_cache = _65_1085.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _65_1085.sigtab; is_pattern = _65_1085.is_pattern; instantiate_imp = _65_1085.instantiate_imp; effects = _65_1085.effects; generalize = _65_1085.generalize; letrecs = _65_1085.letrecs; top_level = _65_1085.top_level; check_uvars = _65_1085.check_uvars; use_eq = _65_1085.use_eq; is_iface = _65_1085.is_iface; admit = _65_1085.admit; default_effects = _65_1085.default_effects; type_of = _65_1085.type_of; universe_of = _65_1085.universe_of; use_bv_sorts = _65_1085.use_bv_sorts})))

# 729 "FStar.TypeChecker.Env.fst"
let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))

# 732 "FStar.TypeChecker.Env.fst"
let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (
# 733 "FStar.TypeChecker.Env.fst"
let _65_1093 = env
in {solver = _65_1093.solver; range = _65_1093.range; curmodule = _65_1093.curmodule; gamma = _65_1093.gamma; gamma_cache = _65_1093.gamma_cache; modules = _65_1093.modules; expected_typ = Some (t); sigtab = _65_1093.sigtab; is_pattern = _65_1093.is_pattern; instantiate_imp = _65_1093.instantiate_imp; effects = _65_1093.effects; generalize = _65_1093.generalize; letrecs = _65_1093.letrecs; top_level = _65_1093.top_level; check_uvars = _65_1093.check_uvars; use_eq = false; is_iface = _65_1093.is_iface; admit = _65_1093.admit; default_effects = _65_1093.default_effects; type_of = _65_1093.type_of; universe_of = _65_1093.universe_of; use_bv_sorts = _65_1093.use_bv_sorts}))

# 735 "FStar.TypeChecker.Env.fst"
let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

# 739 "FStar.TypeChecker.Env.fst"
let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _146_1041 = (expected_typ env)
in ((
# 740 "FStar.TypeChecker.Env.fst"
let _65_1100 = env
in {solver = _65_1100.solver; range = _65_1100.range; curmodule = _65_1100.curmodule; gamma = _65_1100.gamma; gamma_cache = _65_1100.gamma_cache; modules = _65_1100.modules; expected_typ = None; sigtab = _65_1100.sigtab; is_pattern = _65_1100.is_pattern; instantiate_imp = _65_1100.instantiate_imp; effects = _65_1100.effects; generalize = _65_1100.generalize; letrecs = _65_1100.letrecs; top_level = _65_1100.top_level; check_uvars = _65_1100.check_uvars; use_eq = false; is_iface = _65_1100.is_iface; admit = _65_1100.admit; default_effects = _65_1100.default_effects; type_of = _65_1100.type_of; universe_of = _65_1100.universe_of; use_bv_sorts = _65_1100.use_bv_sorts}), _146_1041)))

# 742 "FStar.TypeChecker.Env.fst"
let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (
# 743 "FStar.TypeChecker.Env.fst"
let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (
# 745 "FStar.TypeChecker.Env.fst"
let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(FStar_All.pipe_right env.gamma (FStar_List.collect (fun _65_10 -> (match (_65_10) with
| Binding_sig (_65_1107, se) -> begin
(se)::[]
end
| _65_1112 -> begin
[]
end))))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (
# 751 "FStar.TypeChecker.Env.fst"
let _65_1114 = (add_sigelts env sigs)
in (
# 752 "FStar.TypeChecker.Env.fst"
let _65_1116 = (FStar_Util.smap_clear env.gamma_cache)
in (
# 753 "FStar.TypeChecker.Env.fst"
let _65_1118 = env
in {solver = _65_1118.solver; range = _65_1118.range; curmodule = empty_lid; gamma = []; gamma_cache = _65_1118.gamma_cache; modules = (m)::env.modules; expected_typ = _65_1118.expected_typ; sigtab = _65_1118.sigtab; is_pattern = _65_1118.is_pattern; instantiate_imp = _65_1118.instantiate_imp; effects = _65_1118.effects; generalize = _65_1118.generalize; letrecs = _65_1118.letrecs; top_level = _65_1118.top_level; check_uvars = _65_1118.check_uvars; use_eq = _65_1118.use_eq; is_iface = _65_1118.is_iface; admit = _65_1118.admit; default_effects = _65_1118.default_effects; type_of = _65_1118.type_of; universe_of = _65_1118.universe_of; use_bv_sorts = _65_1118.use_bv_sorts}))))))

# 761 "FStar.TypeChecker.Env.fst"
let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (
# 762 "FStar.TypeChecker.Env.fst"
let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (
# 763 "FStar.TypeChecker.Env.fst"
let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (
# 764 "FStar.TypeChecker.Env.fst"
let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| Binding_univ (_65_1131)::tl -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _146_1058 = (let _146_1057 = (FStar_Syntax_Free.uvars t)
in (ext out _146_1057))
in (aux _146_1058 tl))
end
| (Binding_sig (_)::_) | (Binding_sig_inst (_)::_) -> begin
out
end))
in (aux no_uvs env.gamma)))))

# 773 "FStar.TypeChecker.Env.fst"
let univ_vars : env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun env -> (
# 774 "FStar.TypeChecker.Env.fst"
let no_univs = FStar_Syntax_Syntax.no_universe_uvars
in (
# 775 "FStar.TypeChecker.Env.fst"
let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (
# 776 "FStar.TypeChecker.Env.fst"
let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_sig_inst (_)::tl) | (Binding_univ (_)::tl) -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _146_1070 = (let _146_1069 = (FStar_Syntax_Free.univs t)
in (ext out _146_1069))
in (aux _146_1070 tl))
end
| Binding_sig (_65_1201)::_65_1199 -> begin
out
end))
in (aux no_univs env.gamma)))))

# 785 "FStar.TypeChecker.Env.fst"
let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _65_11 -> (match (_65_11) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))

# 793 "FStar.TypeChecker.Env.fst"
let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _146_1077 = (let _146_1076 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _146_1076 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _146_1077 FStar_List.rev)))

# 795 "FStar.TypeChecker.Env.fst"
let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))

# 797 "FStar.TypeChecker.Env.fst"
let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))

# 799 "FStar.TypeChecker.Env.fst"
let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))

# 801 "FStar.TypeChecker.Env.fst"
let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (
# 802 "FStar.TypeChecker.Env.fst"
let keys = (FStar_List.fold_left (fun keys _65_12 -> (match (_65_12) with
| Binding_sig (lids, _65_1233) -> begin
(FStar_List.append lids keys)
end
| _65_1237 -> begin
keys
end)) [] env.gamma)
in (let _146_1101 = (sigtab env)
in (FStar_Util.smap_fold _146_1101 (fun _65_1239 v keys -> (let _146_1100 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _146_1100 keys))) keys))))

# 809 "FStar.TypeChecker.Env.fst"
let dummy_solver : solver_t = {init = (fun _65_1243 -> ()); push = (fun _65_1245 -> ()); pop = (fun _65_1247 -> ()); mark = (fun _65_1249 -> ()); reset_mark = (fun _65_1251 -> ()); commit_mark = (fun _65_1253 -> ()); encode_modul = (fun _65_1255 _65_1257 -> ()); encode_sig = (fun _65_1259 _65_1261 -> ()); solve = (fun _65_1263 _65_1265 -> ()); is_trivial = (fun _65_1267 _65_1269 -> false); finish = (fun _65_1271 -> ()); refresh = (fun _65_1272 -> ())}

# 824 "FStar.TypeChecker.Env.fst"
let no_solver_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t))  ->  env = (fun tc -> (let _146_1130 = (FStar_Ident.lid_of_path (("dummy")::[]) FStar_Range.dummyRange)
in (initial_env tc dummy_solver _146_1130)))




