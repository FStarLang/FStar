
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
| Binding_var (_52_15) -> begin
_52_15
end))

# 32 "FStar.TypeChecker.Env.fst"
let ___Binding_lid____0 = (fun projectee -> (match (projectee) with
| Binding_lid (_52_18) -> begin
_52_18
end))

# 33 "FStar.TypeChecker.Env.fst"
let ___Binding_sig____0 = (fun projectee -> (match (projectee) with
| Binding_sig (_52_21) -> begin
_52_21
end))

# 34 "FStar.TypeChecker.Env.fst"
let ___Binding_univ____0 = (fun projectee -> (match (projectee) with
| Binding_univ (_52_24) -> begin
_52_24
end))

# 35 "FStar.TypeChecker.Env.fst"
let ___Binding_sig_inst____0 = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_52_27) -> begin
_52_27
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
| Unfold (_52_30) -> begin
_52_30
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
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ Prims.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t); universe_of : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe; use_bv_sorts : Prims.bool} 
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
| _52_100 -> begin
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
| (FStar_Syntax_Syntax.Delta_abstract (l1), _52_149) -> begin
(aux l1 l2)
end
| (_52_152, FStar_Syntax_Syntax.Delta_abstract (l2)) -> begin
(aux l1 l2)
end))
in (let _141_387 = (aux l1 l2)
in Unfold (_141_387)))
end))

# 189 "FStar.TypeChecker.Env.fst"
let default_table_size : Prims.int = 200

# 190 "FStar.TypeChecker.Env.fst"
let new_sigtab = (fun _52_156 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))

# 191 "FStar.TypeChecker.Env.fst"
let new_gamma_cache = (fun _52_157 -> (match (()) with
| () -> begin
(FStar_Util.smap_create 100)
end))

# 193 "FStar.TypeChecker.Env.fst"
let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun tc solver module_lid -> (let _141_409 = (new_gamma_cache ())
in (let _141_408 = (new_sigtab ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _141_409; modules = []; expected_typ = None; sigtab = _141_408; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; type_of = tc; universe_of = (fun g e -> FStar_Syntax_Syntax.U_zero); use_bv_sorts = false})))

# 218 "FStar.TypeChecker.Env.fst"
let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)

# 219 "FStar.TypeChecker.Env.fst"
let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)

# 220 "FStar.TypeChecker.Env.fst"
type env_stack_ops =
{es_push : env  ->  env; es_mark : env  ->  env; es_reset_mark : env  ->  env; es_commit_mark : env  ->  env; es_pop : env  ->  env}

# 220 "FStar.TypeChecker.Env.fst"
let is_Mkenv_stack_ops : env_stack_ops  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_stack_ops"))))

# 228 "FStar.TypeChecker.Env.fst"
let stack_ops : env_stack_ops = (
# 229 "FStar.TypeChecker.Env.fst"
let stack = (FStar_Util.mk_ref [])
in (
# 230 "FStar.TypeChecker.Env.fst"
let push = (fun env -> (
# 231 "FStar.TypeChecker.Env.fst"
let _52_174 = (let _141_463 = (let _141_462 = (FStar_ST.read stack)
in (env)::_141_462)
in (FStar_ST.op_Colon_Equals stack _141_463))
in (
# 232 "FStar.TypeChecker.Env.fst"
let _52_176 = env
in (let _141_465 = (FStar_Util.smap_copy (gamma_cache env))
in (let _141_464 = (FStar_Util.smap_copy (sigtab env))
in {solver = _52_176.solver; range = _52_176.range; curmodule = _52_176.curmodule; gamma = _52_176.gamma; gamma_cache = _141_465; modules = _52_176.modules; expected_typ = _52_176.expected_typ; sigtab = _141_464; is_pattern = _52_176.is_pattern; instantiate_imp = _52_176.instantiate_imp; effects = _52_176.effects; generalize = _52_176.generalize; letrecs = _52_176.letrecs; top_level = _52_176.top_level; check_uvars = _52_176.check_uvars; use_eq = _52_176.use_eq; is_iface = _52_176.is_iface; admit = _52_176.admit; type_of = _52_176.type_of; universe_of = _52_176.universe_of; use_bv_sorts = _52_176.use_bv_sorts})))))
in (
# 234 "FStar.TypeChecker.Env.fst"
let pop = (fun env -> (match ((FStar_ST.read stack)) with
| env::tl -> begin
(
# 236 "FStar.TypeChecker.Env.fst"
let _52_183 = (FStar_ST.op_Colon_Equals stack tl)
in env)
end
| _52_186 -> begin
(FStar_All.failwith "Impossible: Too many pops")
end))
in (
# 239 "FStar.TypeChecker.Env.fst"
let mark = (fun env -> (push env))
in (
# 241 "FStar.TypeChecker.Env.fst"
let commit_mark = (fun env -> (
# 242 "FStar.TypeChecker.Env.fst"
let _52_191 = (let _141_472 = (pop env)
in (Prims.ignore _141_472))
in env))
in (
# 243 "FStar.TypeChecker.Env.fst"
let reset_mark = (fun env -> (pop env))
in {es_push = push; es_mark = push; es_reset_mark = pop; es_commit_mark = commit_mark; es_pop = pop}))))))

# 251 "FStar.TypeChecker.Env.fst"
let push : env  ->  Prims.string  ->  env = (fun env msg -> (
# 252 "FStar.TypeChecker.Env.fst"
let _52_197 = (env.solver.push msg)
in (stack_ops.es_push env)))

# 254 "FStar.TypeChecker.Env.fst"
let mark : env  ->  env = (fun env -> (
# 255 "FStar.TypeChecker.Env.fst"
let _52_200 = (env.solver.mark "USER MARK")
in (stack_ops.es_mark env)))

# 257 "FStar.TypeChecker.Env.fst"
let commit_mark : env  ->  env = (fun env -> (
# 258 "FStar.TypeChecker.Env.fst"
let _52_203 = (env.solver.commit_mark "USER MARK")
in (stack_ops.es_commit_mark env)))

# 260 "FStar.TypeChecker.Env.fst"
let reset_mark : env  ->  env = (fun env -> (
# 261 "FStar.TypeChecker.Env.fst"
let _52_206 = (env.solver.reset_mark "USER MARK")
in (stack_ops.es_reset_mark env)))

# 263 "FStar.TypeChecker.Env.fst"
let pop : env  ->  Prims.string  ->  env = (fun env msg -> (
# 264 "FStar.TypeChecker.Env.fst"
let _52_210 = (env.solver.pop msg)
in (stack_ops.es_pop env)))

# 270 "FStar.TypeChecker.Env.fst"
let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> ((let _141_494 = (FStar_ST.read FStar_Options.debug)
in (FStar_All.pipe_right _141_494 (FStar_Util.for_some (fun x -> ((env.curmodule.FStar_Ident.str = "") || (env.curmodule.FStar_Ident.str = x)))))) && (FStar_Options.debug_level_geq l)))

# 273 "FStar.TypeChecker.Env.fst"
let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(
# 273 "FStar.TypeChecker.Env.fst"
let _52_217 = e
in {solver = _52_217.solver; range = r; curmodule = _52_217.curmodule; gamma = _52_217.gamma; gamma_cache = _52_217.gamma_cache; modules = _52_217.modules; expected_typ = _52_217.expected_typ; sigtab = _52_217.sigtab; is_pattern = _52_217.is_pattern; instantiate_imp = _52_217.instantiate_imp; effects = _52_217.effects; generalize = _52_217.generalize; letrecs = _52_217.letrecs; top_level = _52_217.top_level; check_uvars = _52_217.check_uvars; use_eq = _52_217.use_eq; is_iface = _52_217.is_iface; admit = _52_217.admit; type_of = _52_217.type_of; universe_of = _52_217.universe_of; use_bv_sorts = _52_217.use_bv_sorts})
end)

# 274 "FStar.TypeChecker.Env.fst"
let get_range : env  ->  FStar_Range.range = (fun e -> e.range)

# 279 "FStar.TypeChecker.Env.fst"
let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)

# 280 "FStar.TypeChecker.Env.fst"
let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)

# 281 "FStar.TypeChecker.Env.fst"
let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (
# 281 "FStar.TypeChecker.Env.fst"
let _52_224 = env
in {solver = _52_224.solver; range = _52_224.range; curmodule = lid; gamma = _52_224.gamma; gamma_cache = _52_224.gamma_cache; modules = _52_224.modules; expected_typ = _52_224.expected_typ; sigtab = _52_224.sigtab; is_pattern = _52_224.is_pattern; instantiate_imp = _52_224.instantiate_imp; effects = _52_224.effects; generalize = _52_224.generalize; letrecs = _52_224.letrecs; top_level = _52_224.top_level; check_uvars = _52_224.check_uvars; use_eq = _52_224.use_eq; is_iface = _52_224.is_iface; admit = _52_224.admit; type_of = _52_224.type_of; universe_of = _52_224.universe_of; use_bv_sorts = _52_224.use_bv_sorts}))

# 282 "FStar.TypeChecker.Env.fst"
let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))

# 283 "FStar.TypeChecker.Env.fst"
let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))

# 285 "FStar.TypeChecker.Env.fst"
let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))

# 288 "FStar.TypeChecker.Env.fst"
let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _141_522 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _141_522)))

# 292 "FStar.TypeChecker.Env.fst"
let new_u_univ = (fun _52_233 -> (let _141_524 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_141_524)))

# 295 "FStar.TypeChecker.Env.fst"
let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match ((ts, us)) with
| (([], t), []) -> begin
([], t)
end
| ((formals, t), _52_246) -> begin
(
# 299 "FStar.TypeChecker.Env.fst"
let _52_248 = ()
in (
# 300 "FStar.TypeChecker.Env.fst"
let n = ((FStar_List.length formals) - 1)
in (
# 301 "FStar.TypeChecker.Env.fst"
let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN (((n - i), u)))))
in (let _141_531 = (FStar_Syntax_Subst.subst vs t)
in (us, _141_531)))))
end))

# 305 "FStar.TypeChecker.Env.fst"
let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _52_1 -> (match (_52_1) with
| ([], t) -> begin
([], t)
end
| (us, t) -> begin
(
# 308 "FStar.TypeChecker.Env.fst"
let us' = (FStar_All.pipe_right us (FStar_List.map (fun _52_261 -> (new_u_univ ()))))
in (inst_tscheme_with (us, t) us'))
end))

# 311 "FStar.TypeChecker.Env.fst"
let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed _52_269 -> (match (_52_269) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(
# 314 "FStar.TypeChecker.Env.fst"
let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in (
# 315 "FStar.TypeChecker.Env.fst"
let _52_272 = if ((FStar_List.length insts) <> (FStar_List.length univs)) then begin
(let _141_547 = (let _141_546 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _141_545 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _141_544 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _141_543 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _141_546 _141_545 _141_544 _141_543)))))
in (FStar_All.failwith _141_547))
end else begin
()
end
in (let _141_548 = (inst_tscheme_with ((FStar_List.append ed.FStar_Syntax_Syntax.univs us), t) insts)
in (Prims.snd _141_548))))
end
| _52_275 -> begin
(let _141_550 = (let _141_549 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _141_549))
in (FStar_All.failwith _141_550))
end)
end))

# 322 "FStar.TypeChecker.Env.fst"
type tri =
| Yes
| No
| Maybe

# 323 "FStar.TypeChecker.Env.fst"
let is_Yes = (fun _discr_ -> (match (_discr_) with
| Yes (_) -> begin
true
end
| _ -> begin
false
end))

# 324 "FStar.TypeChecker.Env.fst"
let is_No = (fun _discr_ -> (match (_discr_) with
| No (_) -> begin
true
end
| _ -> begin
false
end))

# 325 "FStar.TypeChecker.Env.fst"
let is_Maybe = (fun _discr_ -> (match (_discr_) with
| Maybe (_) -> begin
true
end
| _ -> begin
false
end))

# 327 "FStar.TypeChecker.Env.fst"
let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (
# 328 "FStar.TypeChecker.Env.fst"
let cur = (current_module env)
in if (l.FStar_Ident.nsstr = cur.FStar_Ident.str) then begin
Yes
end else begin
if (FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str) then begin
(
# 331 "FStar.TypeChecker.Env.fst"
let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (
# 332 "FStar.TypeChecker.Env.fst"
let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (
# 333 "FStar.TypeChecker.Env.fst"
let rec aux = (fun c l -> (match ((c, l)) with
| ([], _52_286) -> begin
Maybe
end
| (_52_289, []) -> begin
No
end
| (hd::tl, hd'::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _52_300 -> begin
No
end))
in (aux cur lns))))
end else begin
No
end
end))

# 341 "FStar.TypeChecker.Env.fst"
let lookup_qname : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either Prims.option = (fun env lid -> (
# 342 "FStar.TypeChecker.Env.fst"
let cur_mod = (in_cur_mod env lid)
in (
# 343 "FStar.TypeChecker.Env.fst"
let cache = (fun t -> (
# 343 "FStar.TypeChecker.Env.fst"
let _52_306 = (FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t)
in Some (t)))
in (
# 344 "FStar.TypeChecker.Env.fst"
let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _52_2 -> (match (_52_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _141_570 = (let _141_569 = (inst_tscheme t)
in FStar_Util.Inl (_141_569))
in Some (_141_570))
end else begin
None
end
end
| Binding_sig (_52_315, FStar_Syntax_Syntax.Sig_bundle (ses, _52_318, _52_320, _52_322)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _141_572 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _141_572 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr ((se, None))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(
# 355 "FStar.TypeChecker.Env.fst"
let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_335) -> begin
Some (t)
end
| _52_338 -> begin
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
| _52_345 -> begin
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

# 372 "FStar.TypeChecker.Env.fst"
let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| None -> begin
false
end
| Some (_52_355) -> begin
true
end))

# 376 "FStar.TypeChecker.Env.fst"
let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _52_361, _52_363, _52_365) -> begin
(add_sigelts env ses)
end
| _52_369 -> begin
(
# 379 "FStar.TypeChecker.Env.fst"
let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))

# 388 "FStar.TypeChecker.Env.fst"
let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun _52_3 -> (match (_52_3) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _52_380 -> begin
None
end))))

# 394 "FStar.TypeChecker.Env.fst"
let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _52_4 -> (match (_52_4) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _52_387 -> begin
false
end)) env.gamma) FStar_Option.isSome))

# 400 "FStar.TypeChecker.Env.fst"
let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_391, lb::[]), _52_396, _52_398, _52_400) -> begin
(let _141_605 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_141_605))
end
| FStar_Syntax_Syntax.Sig_let ((_52_404, lbs), _52_408, _52_410, _52_412) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_52_417) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _141_607 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_141_607))
end else begin
None
end
end)))
end
| _52_422 -> begin
None
end))

# 414 "FStar.TypeChecker.Env.fst"
let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _141_615 = (let _141_614 = (let _141_613 = (variable_not_found bv)
in (let _141_612 = (FStar_Syntax_Syntax.range_of_bv bv)
in (_141_613, _141_612)))
in FStar_Syntax_Syntax.Error (_141_614))
in (Prims.raise _141_615))
end
| Some (t) -> begin
t
end))

# 419 "FStar.TypeChecker.Env.fst"
let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_431) -> begin
(let _141_621 = (let _141_620 = (let _141_619 = (let _141_618 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _141_618))
in (ne.FStar_Syntax_Syntax.univs, _141_619))
in (inst_tscheme _141_620))
in Some (_141_621))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _52_438, _52_440, _52_442) -> begin
(let _141_625 = (let _141_624 = (let _141_623 = (let _141_622 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _141_622))
in (us, _141_623))
in (inst_tscheme _141_624))
in Some (_141_625))
end
| _52_446 -> begin
None
end))

# 429 "FStar.TypeChecker.Env.fst"
let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_52_456, t) -> begin
Some (t)
end)
end
| _52_461 -> begin
None
end))

# 438 "FStar.TypeChecker.Env.fst"
let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env lid -> (
# 439 "FStar.TypeChecker.Env.fst"
let mapper = (fun _52_5 -> (match (_52_5) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_468, uvs, t, _52_472, _52_474, _52_476, _52_478, _52_480), None) -> begin
(let _141_636 = (inst_tscheme (uvs, t))
in Some (_141_636))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _52_491), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _141_637 = (inst_tscheme (uvs, t))
in Some (_141_637))
end else begin
None
end
end else begin
(let _141_638 = (inst_tscheme (uvs, t))
in Some (_141_638))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_502, _52_504, _52_506, _52_508), None) -> begin
(match (tps) with
| [] -> begin
(let _141_640 = (inst_tscheme (uvs, k))
in (FStar_All.pipe_left (fun _141_639 -> Some (_141_639)) _141_640))
end
| _52_516 -> begin
(let _141_645 = (let _141_644 = (let _141_643 = (let _141_642 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _141_642))
in (uvs, _141_643))
in (inst_tscheme _141_644))
in (FStar_All.pipe_left (fun _141_641 -> Some (_141_641)) _141_645))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _52_522, _52_524, _52_526, _52_528), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _141_647 = (inst_tscheme_with (uvs, k) us)
in (FStar_All.pipe_left (fun _141_646 -> Some (_141_646)) _141_647))
end
| _52_537 -> begin
(let _141_652 = (let _141_651 = (let _141_650 = (let _141_649 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _141_649))
in (uvs, _141_650))
in (inst_tscheme_with _141_651 us))
in (FStar_All.pipe_left (fun _141_648 -> Some (_141_648)) _141_652))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_52_541), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _52_546 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _141_653 = (lookup_qname env lid)
in (FStar_Util.bind_opt _141_653 mapper))) with
| Some (us, t) -> begin
Some ((us, (
# 473 "FStar.TypeChecker.Env.fst"
let _52_552 = t
in {FStar_Syntax_Syntax.n = _52_552.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _52_552.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _52_552.FStar_Syntax_Syntax.vars})))
end
| None -> begin
None
end)))

# 476 "FStar.TypeChecker.Env.fst"
let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (
# 477 "FStar.TypeChecker.Env.fst"
let mapper = (fun _52_6 -> (match (_52_6) with
| FStar_Util.Inl (_52_559) -> begin
Some (false)
end
| FStar_Util.Inr (se, _52_563) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (_52_567, _52_569, _52_571, qs, _52_574) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (_52_578) -> begin
Some (true)
end
| _52_581 -> begin
Some (false)
end)
end))
in (match ((let _141_660 = (lookup_qname env lid)
in (FStar_Util.bind_opt _141_660 mapper))) with
| Some (b) -> begin
b
end
| None -> begin
false
end)))

# 492 "FStar.TypeChecker.Env.fst"
let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _141_667 = (let _141_666 = (let _141_665 = (name_not_found l)
in (_141_665, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_141_666))
in (Prims.raise _141_667))
end
| Some (x) -> begin
x
end))

# 497 "FStar.TypeChecker.Env.fst"
let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_594, uvs, t, _52_598, _52_600), None)) -> begin
(inst_tscheme (uvs, t))
end
| _52_608 -> begin
(let _141_674 = (let _141_673 = (let _141_672 = (name_not_found lid)
in (_141_672, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_141_673))
in (Prims.raise _141_674))
end))

# 502 "FStar.TypeChecker.Env.fst"
let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_612, uvs, t, _52_616, _52_618, _52_620, _52_622, _52_624), None)) -> begin
(inst_tscheme (uvs, t))
end
| _52_632 -> begin
(let _141_681 = (let _141_680 = (let _141_679 = (name_not_found lid)
in (_141_679, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_141_680))
in (Prims.raise _141_681))
end))

# 507 "FStar.TypeChecker.Env.fst"
let lookup_definition : delta_level  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_52_642, lbs), _52_646, _52_648, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (
# 513 "FStar.TypeChecker.Env.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _141_690 = (let _141_689 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (lb.FStar_Syntax_Syntax.lbunivs, _141_689))
in Some (_141_690))
end else begin
None
end)))
end
| _52_655 -> begin
None
end)
end
| _52_657 -> begin
None
end))

# 521 "FStar.TypeChecker.Env.fst"
let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _141_697 = (let _141_696 = (let _141_695 = (name_not_found ftv)
in (_141_695, (FStar_Ident.range_of_lid ftv)))
in FStar_Syntax_Syntax.Error (_141_696))
in (Prims.raise _141_697))
end
| Some (k) -> begin
k
end))

# 526 "FStar.TypeChecker.Env.fst"
let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (
# 527 "FStar.TypeChecker.Env.fst"
let fail = (fun _52_667 -> (match (()) with
| () -> begin
(let _141_708 = (let _141_707 = (FStar_Util.string_of_int i)
in (let _141_706 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _141_707 _141_706)))
in (FStar_All.failwith _141_708))
end))
in (
# 528 "FStar.TypeChecker.Env.fst"
let _52_671 = (lookup_datacon env lid)
in (match (_52_671) with
| (_52_669, t) -> begin
(match ((let _141_709 = (FStar_Syntax_Subst.compress t)
in _141_709.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _52_674) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(
# 533 "FStar.TypeChecker.Env.fst"
let b = (FStar_List.nth binders i)
in (let _141_710 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _141_710 Prims.fst)))
end
end
| _52_679 -> begin
(fail ())
end)
end))))

# 537 "FStar.TypeChecker.Env.fst"
let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_683, uvs, t, q, _52_688), None)) -> begin
Some (((uvs, t), q))
end
| _52_696 -> begin
None
end))

# 542 "FStar.TypeChecker.Env.fst"
let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _52_706), None)) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _52_7 -> (match (_52_7) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _52_716 -> begin
false
end)))) then begin
None
end else begin
(
# 547 "FStar.TypeChecker.Env.fst"
let insts = if (FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid) then begin
(univ)::(FStar_Syntax_Syntax.U_zero)::[]
end else begin
(univ)::[]
end
in (match ((binders, univs)) with
| ([], _52_720) -> begin
(FStar_All.failwith "Unexpected effect abbreviation with no arguments")
end
| (_52_723, _52_730::_52_727::_52_725) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(let _141_724 = (let _141_723 = (FStar_Syntax_Print.lid_to_string lid)
in (let _141_722 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _141_723 _141_722)))
in (FStar_All.failwith _141_724))
end
| _52_734 -> begin
(
# 555 "FStar.TypeChecker.Env.fst"
let _52_738 = (let _141_726 = (let _141_725 = (FStar_Syntax_Util.arrow binders c)
in (univs, _141_725))
in (inst_tscheme_with _141_726 insts))
in (match (_52_738) with
| (_52_736, t) -> begin
(match ((let _141_727 = (FStar_Syntax_Subst.compress t)
in _141_727.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some ((binders, c))
end
| _52_744 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end))
end
end
| _52_746 -> begin
None
end))

# 564 "FStar.TypeChecker.Env.fst"
let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (
# 565 "FStar.TypeChecker.Env.fst"
let cache = (FStar_Util.smap_create 20)
in (fun env l -> (
# 567 "FStar.TypeChecker.Env.fst"
let rec find = (fun l -> (match ((lookup_effect_abbrev env FStar_Syntax_Syntax.U_unknown l)) with
| None -> begin
None
end
| Some (_52_754, c) -> begin
(
# 571 "FStar.TypeChecker.Env.fst"
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
# 575 "FStar.TypeChecker.Env.fst"
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
# 580 "FStar.TypeChecker.Env.fst"
let _52_768 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

# 585 "FStar.TypeChecker.Env.fst"
let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_774, _52_776, _52_778, _52_780, _52_782, dcs, _52_785, _52_787), _52_791)) -> begin
dcs
end
| _52_796 -> begin
[]
end))

# 590 "FStar.TypeChecker.Env.fst"
let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_800, _52_802, _52_804, l, _52_807, _52_809, _52_811, _52_813), _52_817)) -> begin
l
end
| _52_822 -> begin
(let _141_743 = (let _141_742 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _141_742))
in (FStar_All.failwith _141_743))
end))

# 595 "FStar.TypeChecker.Env.fst"
let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_52_826, _52_828, _52_830, _52_832, _52_834, _52_836, _52_838, _52_840), _52_844)) -> begin
true
end
| _52_849 -> begin
false
end))

# 600 "FStar.TypeChecker.Env.fst"
let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_52_853, _52_855, _52_857, _52_859, _52_861, _52_863, tags, _52_866), _52_870)) -> begin
(FStar_Util.for_some (fun _52_8 -> (match (_52_8) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _52_882 -> begin
false
end)) tags)
end
| _52_884 -> begin
false
end))

# 606 "FStar.TypeChecker.Env.fst"
let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_52_888, _52_890, _52_892, quals, _52_895), _52_899)) -> begin
(FStar_Util.for_some (fun _52_9 -> (match (_52_9) with
| FStar_Syntax_Syntax.Projector (_52_905) -> begin
true
end
| _52_908 -> begin
false
end)) quals)
end
| _52_910 -> begin
false
end))

# 612 "FStar.TypeChecker.Env.fst"
let interpreted_symbols : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]

# 629 "FStar.TypeChecker.Env.fst"
let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env head -> (match ((let _141_762 = (FStar_Syntax_Util.un_uinst head)
in _141_762.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _52_916 -> begin
false
end))

# 639 "FStar.TypeChecker.Env.fst"
let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))

# 642 "FStar.TypeChecker.Env.fst"
let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _141_774 = (let _141_773 = (let _141_772 = (name_not_found l)
in (_141_772, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_141_773))
in (Prims.raise _141_774))
end
| Some (md) -> begin
md
end))

# 647 "FStar.TypeChecker.Env.fst"
let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
(l1, (fun t wp -> wp), (fun t wp -> wp))
end else begin
if (((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid))) then begin
(FStar_Syntax_Const.effect_GTot_lid, (fun t wp -> wp), (fun t wp -> wp))
end else begin
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _52_944 -> (match (_52_944) with
| (m1, m2, _52_939, _52_941, _52_943) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _141_850 = (let _141_849 = (let _141_848 = (let _141_847 = (FStar_Syntax_Print.lid_to_string l1)
in (let _141_846 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _141_847 _141_846)))
in (_141_848, env.range))
in FStar_Syntax_Syntax.Error (_141_849))
in (Prims.raise _141_850))
end
| Some (_52_947, _52_949, m3, j1, j2) -> begin
(m3, j1, j2)
end)
end
end)

# 657 "FStar.TypeChecker.Env.fst"
let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge Prims.option = (fun env l1 l2 -> if ((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid))) then begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end else begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end)

# 663 "FStar.TypeChecker.Env.fst"
let wp_sig_aux : FStar_Syntax_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun decls m -> (match ((FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))))) with
| None -> begin
(let _141_865 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _141_865))
end
| Some (md) -> begin
(
# 667 "FStar.TypeChecker.Env.fst"
let _52_970 = (inst_tscheme (md.FStar_Syntax_Syntax.univs, md.FStar_Syntax_Syntax.signature))
in (match (_52_970) with
| (_52_968, s) -> begin
(
# 668 "FStar.TypeChecker.Env.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match ((md.FStar_Syntax_Syntax.binders, s.FStar_Syntax_Syntax.n)) with
| ([], FStar_Syntax_Syntax.Tm_arrow ((a, _52_983)::(wp, _52_979)::(wlp, _52_975)::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _52_991 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))

# 673 "FStar.TypeChecker.Env.fst"
let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))

# 675 "FStar.TypeChecker.Env.fst"
let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _52_998) -> begin
(
# 677 "FStar.TypeChecker.Env.fst"
let effects = (
# 677 "FStar.TypeChecker.Env.fst"
let _52_1001 = env.effects
in {decls = (ne)::env.effects.decls; order = _52_1001.order; joins = _52_1001.joins})
in (
# 678 "FStar.TypeChecker.Env.fst"
let _52_1004 = env
in {solver = _52_1004.solver; range = _52_1004.range; curmodule = _52_1004.curmodule; gamma = _52_1004.gamma; gamma_cache = _52_1004.gamma_cache; modules = _52_1004.modules; expected_typ = _52_1004.expected_typ; sigtab = _52_1004.sigtab; is_pattern = _52_1004.is_pattern; instantiate_imp = _52_1004.instantiate_imp; effects = effects; generalize = _52_1004.generalize; letrecs = _52_1004.letrecs; top_level = _52_1004.top_level; check_uvars = _52_1004.check_uvars; use_eq = _52_1004.use_eq; is_iface = _52_1004.is_iface; admit = _52_1004.admit; type_of = _52_1004.type_of; universe_of = _52_1004.universe_of; use_bv_sorts = _52_1004.use_bv_sorts}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _52_1008) -> begin
(
# 681 "FStar.TypeChecker.Env.fst"
let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _141_880 = (e1.mlift r wp1)
in (e2.mlift r _141_880)))})
in (
# 686 "FStar.TypeChecker.Env.fst"
let mk_lift = (fun lift_t r wp1 -> (
# 687 "FStar.TypeChecker.Env.fst"
let _52_1023 = (inst_tscheme lift_t)
in (match (_52_1023) with
| (_52_1021, lift_t) -> begin
(let _141_892 = (let _141_891 = (let _141_890 = (let _141_889 = (FStar_Syntax_Syntax.as_arg r)
in (let _141_888 = (let _141_887 = (FStar_Syntax_Syntax.as_arg wp1)
in (_141_887)::[])
in (_141_889)::_141_888))
in (lift_t, _141_890))
in FStar_Syntax_Syntax.Tm_app (_141_891))
in (FStar_Syntax_Syntax.mk _141_892 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (
# 690 "FStar.TypeChecker.Env.fst"
let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub.FStar_Syntax_Syntax.lift)}
in (
# 694 "FStar.TypeChecker.Env.fst"
let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (
# 699 "FStar.TypeChecker.Env.fst"
let print_mlift = (fun l -> (
# 700 "FStar.TypeChecker.Env.fst"
let arg = (let _141_909 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _141_909 FStar_Syntax_Syntax.Delta_constant None))
in (
# 701 "FStar.TypeChecker.Env.fst"
let wp = (let _141_910 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _141_910 FStar_Syntax_Syntax.Delta_constant None))
in (let _141_911 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _141_911)))))
in (
# 703 "FStar.TypeChecker.Env.fst"
let order = (edge)::env.effects.order
in (
# 705 "FStar.TypeChecker.Env.fst"
let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (
# 707 "FStar.TypeChecker.Env.fst"
let find_edge = (fun order _52_1040 -> (match (_52_1040) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _141_917 -> Some (_141_917)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (
# 716 "FStar.TypeChecker.Env.fst"
let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _141_925 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _141_924 = (find_edge order (i, k))
in (let _141_923 = (find_edge order (k, j))
in (_141_924, _141_923)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _52_1052 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _141_925))) order))
in (
# 727 "FStar.TypeChecker.Env.fst"
let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (
# 729 "FStar.TypeChecker.Env.fst"
let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (
# 732 "FStar.TypeChecker.Env.fst"
let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _141_1017 = (find_edge order (i, k))
in (let _141_1016 = (find_edge order (j, k))
in (_141_1017, _141_1016)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _52_1069, _52_1071) -> begin
if ((let _141_1018 = (find_edge order (k, ub))
in (FStar_Util.is_some _141_1018)) && (not ((let _141_1019 = (find_edge order (ub, k))
in (FStar_Util.is_some _141_1019))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _52_1075 -> begin
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
# 749 "FStar.TypeChecker.Env.fst"
let effects = (
# 749 "FStar.TypeChecker.Env.fst"
let _52_1084 = env.effects
in {decls = _52_1084.decls; order = order; joins = joins})
in (
# 752 "FStar.TypeChecker.Env.fst"
let _52_1087 = env
in {solver = _52_1087.solver; range = _52_1087.range; curmodule = _52_1087.curmodule; gamma = _52_1087.gamma; gamma_cache = _52_1087.gamma_cache; modules = _52_1087.modules; expected_typ = _52_1087.expected_typ; sigtab = _52_1087.sigtab; is_pattern = _52_1087.is_pattern; instantiate_imp = _52_1087.instantiate_imp; effects = effects; generalize = _52_1087.generalize; letrecs = _52_1087.letrecs; top_level = _52_1087.top_level; check_uvars = _52_1087.check_uvars; use_eq = _52_1087.use_eq; is_iface = _52_1087.is_iface; admit = _52_1087.admit; type_of = _52_1087.type_of; universe_of = _52_1087.universe_of; use_bv_sorts = _52_1087.use_bv_sorts})))))))))))))
end
| _52_1090 -> begin
env
end))

# 759 "FStar.TypeChecker.Env.fst"
let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (let _141_1068 = (
# 759 "FStar.TypeChecker.Env.fst"
let _52_1093 = env
in (let _141_1067 = (let _141_1066 = (let _141_1065 = (let _141_1064 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_141_1064, s))
in Binding_sig (_141_1065))
in (_141_1066)::env.gamma)
in {solver = _52_1093.solver; range = _52_1093.range; curmodule = _52_1093.curmodule; gamma = _141_1067; gamma_cache = _52_1093.gamma_cache; modules = _52_1093.modules; expected_typ = _52_1093.expected_typ; sigtab = _52_1093.sigtab; is_pattern = _52_1093.is_pattern; instantiate_imp = _52_1093.instantiate_imp; effects = _52_1093.effects; generalize = _52_1093.generalize; letrecs = _52_1093.letrecs; top_level = _52_1093.top_level; check_uvars = _52_1093.check_uvars; use_eq = _52_1093.use_eq; is_iface = _52_1093.is_iface; admit = _52_1093.admit; type_of = _52_1093.type_of; universe_of = _52_1093.universe_of; use_bv_sorts = _52_1093.use_bv_sorts}))
in (build_lattice _141_1068 s)))

# 761 "FStar.TypeChecker.Env.fst"
let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (let _141_1079 = (
# 761 "FStar.TypeChecker.Env.fst"
let _52_1098 = env
in (let _141_1078 = (let _141_1077 = (let _141_1076 = (let _141_1075 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_141_1075, s, us))
in Binding_sig_inst (_141_1076))
in (_141_1077)::env.gamma)
in {solver = _52_1098.solver; range = _52_1098.range; curmodule = _52_1098.curmodule; gamma = _141_1078; gamma_cache = _52_1098.gamma_cache; modules = _52_1098.modules; expected_typ = _52_1098.expected_typ; sigtab = _52_1098.sigtab; is_pattern = _52_1098.is_pattern; instantiate_imp = _52_1098.instantiate_imp; effects = _52_1098.effects; generalize = _52_1098.generalize; letrecs = _52_1098.letrecs; top_level = _52_1098.top_level; check_uvars = _52_1098.check_uvars; use_eq = _52_1098.use_eq; is_iface = _52_1098.is_iface; admit = _52_1098.admit; type_of = _52_1098.type_of; universe_of = _52_1098.universe_of; use_bv_sorts = _52_1098.use_bv_sorts}))
in (build_lattice _141_1079 s)))

# 763 "FStar.TypeChecker.Env.fst"
let push_local_binding : env  ->  binding  ->  env = (fun env b -> (
# 763 "FStar.TypeChecker.Env.fst"
let _52_1102 = env
in {solver = _52_1102.solver; range = _52_1102.range; curmodule = _52_1102.curmodule; gamma = (b)::env.gamma; gamma_cache = _52_1102.gamma_cache; modules = _52_1102.modules; expected_typ = _52_1102.expected_typ; sigtab = _52_1102.sigtab; is_pattern = _52_1102.is_pattern; instantiate_imp = _52_1102.instantiate_imp; effects = _52_1102.effects; generalize = _52_1102.generalize; letrecs = _52_1102.letrecs; top_level = _52_1102.top_level; check_uvars = _52_1102.check_uvars; use_eq = _52_1102.use_eq; is_iface = _52_1102.is_iface; admit = _52_1102.admit; type_of = _52_1102.type_of; universe_of = _52_1102.universe_of; use_bv_sorts = _52_1102.use_bv_sorts}))

# 765 "FStar.TypeChecker.Env.fst"
let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))

# 767 "FStar.TypeChecker.Env.fst"
let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _52_1112 -> (match (_52_1112) with
| (x, _52_1111) -> begin
(push_bv env x)
end)) env bs))

# 770 "FStar.TypeChecker.Env.fst"
let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(
# 772 "FStar.TypeChecker.Env.fst"
let _52_1117 = ()
in (
# 773 "FStar.TypeChecker.Env.fst"
let x = (
# 773 "FStar.TypeChecker.Env.fst"
let _52_1119 = x
in {FStar_Syntax_Syntax.ppname = _52_1119.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_1119.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, t))
end))

# 778 "FStar.TypeChecker.Env.fst"
let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))

# 780 "FStar.TypeChecker.Env.fst"
let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (
# 781 "FStar.TypeChecker.Env.fst"
let _52_1129 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (
# 782 "FStar.TypeChecker.Env.fst"
let _52_1131 = env
in {solver = _52_1131.solver; range = _52_1131.range; curmodule = _52_1131.curmodule; gamma = []; gamma_cache = _52_1131.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _52_1131.sigtab; is_pattern = _52_1131.is_pattern; instantiate_imp = _52_1131.instantiate_imp; effects = _52_1131.effects; generalize = _52_1131.generalize; letrecs = _52_1131.letrecs; top_level = _52_1131.top_level; check_uvars = _52_1131.check_uvars; use_eq = _52_1131.use_eq; is_iface = _52_1131.is_iface; admit = _52_1131.admit; type_of = _52_1131.type_of; universe_of = _52_1131.universe_of; use_bv_sorts = _52_1131.use_bv_sorts})))

# 787 "FStar.TypeChecker.Env.fst"
let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))

# 790 "FStar.TypeChecker.Env.fst"
let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (
# 791 "FStar.TypeChecker.Env.fst"
let _52_1139 = env
in {solver = _52_1139.solver; range = _52_1139.range; curmodule = _52_1139.curmodule; gamma = _52_1139.gamma; gamma_cache = _52_1139.gamma_cache; modules = _52_1139.modules; expected_typ = Some (t); sigtab = _52_1139.sigtab; is_pattern = _52_1139.is_pattern; instantiate_imp = _52_1139.instantiate_imp; effects = _52_1139.effects; generalize = _52_1139.generalize; letrecs = _52_1139.letrecs; top_level = _52_1139.top_level; check_uvars = _52_1139.check_uvars; use_eq = false; is_iface = _52_1139.is_iface; admit = _52_1139.admit; type_of = _52_1139.type_of; universe_of = _52_1139.universe_of; use_bv_sorts = _52_1139.use_bv_sorts}))

# 793 "FStar.TypeChecker.Env.fst"
let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

# 797 "FStar.TypeChecker.Env.fst"
let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _141_1122 = (expected_typ env)
in ((
# 798 "FStar.TypeChecker.Env.fst"
let _52_1146 = env
in {solver = _52_1146.solver; range = _52_1146.range; curmodule = _52_1146.curmodule; gamma = _52_1146.gamma; gamma_cache = _52_1146.gamma_cache; modules = _52_1146.modules; expected_typ = None; sigtab = _52_1146.sigtab; is_pattern = _52_1146.is_pattern; instantiate_imp = _52_1146.instantiate_imp; effects = _52_1146.effects; generalize = _52_1146.generalize; letrecs = _52_1146.letrecs; top_level = _52_1146.top_level; check_uvars = _52_1146.check_uvars; use_eq = false; is_iface = _52_1146.is_iface; admit = _52_1146.admit; type_of = _52_1146.type_of; universe_of = _52_1146.universe_of; use_bv_sorts = _52_1146.use_bv_sorts}), _141_1122)))

# 800 "FStar.TypeChecker.Env.fst"
let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (
# 801 "FStar.TypeChecker.Env.fst"
let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (
# 803 "FStar.TypeChecker.Env.fst"
let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(let _141_1128 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _52_10 -> (match (_52_10) with
| Binding_sig (_52_1153, se) -> begin
(se)::[]
end
| _52_1158 -> begin
[]
end))))
in (FStar_All.pipe_right _141_1128 FStar_List.rev))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (
# 809 "FStar.TypeChecker.Env.fst"
let _52_1160 = (add_sigelts env sigs)
in (
# 810 "FStar.TypeChecker.Env.fst"
let _52_1162 = env
in {solver = _52_1162.solver; range = _52_1162.range; curmodule = empty_lid; gamma = []; gamma_cache = _52_1162.gamma_cache; modules = (m)::env.modules; expected_typ = _52_1162.expected_typ; sigtab = _52_1162.sigtab; is_pattern = _52_1162.is_pattern; instantiate_imp = _52_1162.instantiate_imp; effects = _52_1162.effects; generalize = _52_1162.generalize; letrecs = _52_1162.letrecs; top_level = _52_1162.top_level; check_uvars = _52_1162.check_uvars; use_eq = _52_1162.use_eq; is_iface = _52_1162.is_iface; admit = _52_1162.admit; type_of = _52_1162.type_of; universe_of = _52_1162.universe_of; use_bv_sorts = _52_1162.use_bv_sorts})))))

# 818 "FStar.TypeChecker.Env.fst"
let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (
# 819 "FStar.TypeChecker.Env.fst"
let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (
# 820 "FStar.TypeChecker.Env.fst"
let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (
# 821 "FStar.TypeChecker.Env.fst"
let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| Binding_univ (_52_1175)::tl -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _141_1140 = (let _141_1139 = (FStar_Syntax_Free.uvars t)
in (ext out _141_1139))
in (aux _141_1140 tl))
end
| (Binding_sig (_)::_) | (Binding_sig_inst (_)::_) -> begin
out
end))
in (aux no_uvs env.gamma)))))

# 830 "FStar.TypeChecker.Env.fst"
let univ_vars : env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun env -> (
# 831 "FStar.TypeChecker.Env.fst"
let no_univs = FStar_Syntax_Syntax.no_universe_uvars
in (
# 832 "FStar.TypeChecker.Env.fst"
let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (
# 833 "FStar.TypeChecker.Env.fst"
let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_sig_inst (_)::tl) | (Binding_univ (_)::tl) -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _141_1152 = (let _141_1151 = (FStar_Syntax_Free.univs t)
in (ext out _141_1151))
in (aux _141_1152 tl))
end
| Binding_sig (_52_1245)::_52_1243 -> begin
out
end))
in (aux no_univs env.gamma)))))

# 842 "FStar.TypeChecker.Env.fst"
let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _52_11 -> (match (_52_11) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))

# 850 "FStar.TypeChecker.Env.fst"
let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _141_1159 = (let _141_1158 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _141_1158 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _141_1159 FStar_List.rev)))

# 852 "FStar.TypeChecker.Env.fst"
let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))

# 854 "FStar.TypeChecker.Env.fst"
let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))

# 856 "FStar.TypeChecker.Env.fst"
let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))

# 858 "FStar.TypeChecker.Env.fst"
let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (
# 859 "FStar.TypeChecker.Env.fst"
let keys = (FStar_List.fold_left (fun keys _52_12 -> (match (_52_12) with
| Binding_sig (lids, _52_1277) -> begin
(FStar_List.append lids keys)
end
| _52_1281 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun _52_1283 v keys -> (let _141_1182 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _141_1182 keys))) keys)))

# 866 "FStar.TypeChecker.Env.fst"
let dummy_solver : solver_t = {init = (fun _52_1287 -> ()); push = (fun _52_1289 -> ()); pop = (fun _52_1291 -> ()); mark = (fun _52_1293 -> ()); reset_mark = (fun _52_1295 -> ()); commit_mark = (fun _52_1297 -> ()); encode_modul = (fun _52_1299 _52_1301 -> ()); encode_sig = (fun _52_1303 _52_1305 -> ()); solve = (fun _52_1307 _52_1309 _52_1311 -> ()); is_trivial = (fun _52_1313 _52_1315 -> false); finish = (fun _52_1317 -> ()); refresh = (fun _52_1318 -> ())}

# 881 "FStar.TypeChecker.Env.fst"
let no_solver_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  env = (fun tc -> (let _141_1218 = (FStar_Ident.lid_of_path (("dummy")::[]) FStar_Range.dummyRange)
in (initial_env tc dummy_solver _141_1218)))




