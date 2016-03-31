
open Prims

type binding =
| Binding_var of FStar_Syntax_Syntax.bv
| Binding_lid of (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme)
| Binding_sig of (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
| Binding_univ of FStar_Syntax_Syntax.univ_name
| Binding_sig_inst of (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes)


let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))


let is_Binding_lid = (fun _discr_ -> (match (_discr_) with
| Binding_lid (_) -> begin
true
end
| _ -> begin
false
end))


let is_Binding_sig = (fun _discr_ -> (match (_discr_) with
| Binding_sig (_) -> begin
true
end
| _ -> begin
false
end))


let is_Binding_univ = (fun _discr_ -> (match (_discr_) with
| Binding_univ (_) -> begin
true
end
| _ -> begin
false
end))


let is_Binding_sig_inst = (fun _discr_ -> (match (_discr_) with
| Binding_sig_inst (_) -> begin
true
end
| _ -> begin
false
end))


let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_63_16) -> begin
_63_16
end))


let ___Binding_lid____0 = (fun projectee -> (match (projectee) with
| Binding_lid (_63_19) -> begin
_63_19
end))


let ___Binding_sig____0 = (fun projectee -> (match (projectee) with
| Binding_sig (_63_22) -> begin
_63_22
end))


let ___Binding_univ____0 = (fun projectee -> (match (projectee) with
| Binding_univ (_63_25) -> begin
_63_25
end))


let ___Binding_sig_inst____0 = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_63_28) -> begin
_63_28
end))


type delta_level =
| NoDelta
| OnlyInline
| Unfold of FStar_Syntax_Syntax.delta_depth


let is_NoDelta = (fun _discr_ -> (match (_discr_) with
| NoDelta (_) -> begin
true
end
| _ -> begin
false
end))


let is_OnlyInline = (fun _discr_ -> (match (_discr_) with
| OnlyInline (_) -> begin
true
end
| _ -> begin
false
end))


let is_Unfold = (fun _discr_ -> (match (_discr_) with
| Unfold (_) -> begin
true
end
| _ -> begin
false
end))


let ___Unfold____0 = (fun projectee -> (match (projectee) with
| Unfold (_63_31) -> begin
_63_31
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
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ Prims.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap Prims.list; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; default_effects : (FStar_Ident.lident * FStar_Ident.lident) Prims.list; type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t); universe_of : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe; use_bv_sorts : Prims.bool} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit; solve : (Prims.unit  ->  Prims.string) Prims.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit} 
 and guard_t =
{guard_f : FStar_TypeChecker_Common.guard_formula; deferred : FStar_TypeChecker_Common.deferred; univ_ineqs : FStar_TypeChecker_Common.univ_ineq Prims.list; implicits : (Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


let is_Mksolver_t : solver_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksolver_t"))))


let is_Mkguard_t : guard_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkguard_t"))))


type env_t =
env


type implicits =
(env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list


type sigtable =
FStar_Syntax_Syntax.sigelt FStar_Util.smap


let visible_at : delta_level  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun d q -> (match ((d, q)) with
| ((NoDelta, _)) | ((OnlyInline, FStar_Syntax_Syntax.Inline)) | ((Unfold (_), FStar_Syntax_Syntax.Inline)) | ((Unfold (_), FStar_Syntax_Syntax.Unfoldable)) -> begin
true
end
| _63_102 -> begin
false
end))


let glb_delta : delta_level  ->  delta_level  ->  delta_level = (fun d1 d2 -> (match ((d1, d2)) with
| ((NoDelta, _)) | ((_, NoDelta)) -> begin
NoDelta
end
| ((OnlyInline, _)) | ((_, OnlyInline)) -> begin
OnlyInline
end
| (Unfold (l1), Unfold (l2)) -> begin
(

let rec aux = (fun l1 l2 -> (match ((l1, l2)) with
| ((FStar_Syntax_Syntax.Delta_constant, _)) | ((_, FStar_Syntax_Syntax.Delta_constant)) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| ((FStar_Syntax_Syntax.Delta_equational, l)) | ((l, FStar_Syntax_Syntax.Delta_equational)) -> begin
l
end
| (FStar_Syntax_Syntax.Delta_unfoldable (i), FStar_Syntax_Syntax.Delta_unfoldable (j)) -> begin
(

let k = if (i < j) then begin
i
end else begin
j
end
in FStar_Syntax_Syntax.Delta_unfoldable (k))
end
| (FStar_Syntax_Syntax.Delta_abstract (l1), _63_151) -> begin
(aux l1 l2)
end
| (_63_154, FStar_Syntax_Syntax.Delta_abstract (l2)) -> begin
(aux l1 l2)
end))
in (let _152_390 = (aux l1 l2)
in Unfold (_152_390)))
end))


let default_table_size : Prims.int = 200


let new_sigtab = (fun _63_158 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t))  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun tc solver module_lid -> (let _152_412 = (FStar_Util.smap_create 100)
in (let _152_411 = (let _152_408 = (new_sigtab ())
in (_152_408)::[])
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _152_412; modules = []; expected_typ = None; sigtab = _152_411; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []; type_of = tc; universe_of = (fun g e -> FStar_Syntax_Syntax.U_zero); use_bv_sorts = false})))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> (FStar_List.hd env.sigtab))


let push : env  ->  Prims.string  ->  env = (fun env msg -> (

let _63_167 = (env.solver.push msg)
in (

let _63_169 = env
in (let _152_421 = (let _152_420 = (let _152_419 = (sigtab env)
in (FStar_Util.smap_copy _152_419))
in (_152_420)::env.sigtab)
in {solver = _63_169.solver; range = _63_169.range; curmodule = _63_169.curmodule; gamma = _63_169.gamma; gamma_cache = _63_169.gamma_cache; modules = _63_169.modules; expected_typ = _63_169.expected_typ; sigtab = _152_421; is_pattern = _63_169.is_pattern; instantiate_imp = _63_169.instantiate_imp; effects = _63_169.effects; generalize = _63_169.generalize; letrecs = _63_169.letrecs; top_level = _63_169.top_level; check_uvars = _63_169.check_uvars; use_eq = _63_169.use_eq; is_iface = _63_169.is_iface; admit = _63_169.admit; default_effects = _63_169.default_effects; type_of = _63_169.type_of; universe_of = _63_169.universe_of; use_bv_sorts = _63_169.use_bv_sorts}))))


let mark : env  ->  env = (fun env -> (

let _63_172 = (env.solver.mark "USER MARK")
in (

let _63_174 = env
in (let _152_426 = (let _152_425 = (let _152_424 = (sigtab env)
in (FStar_Util.smap_copy _152_424))
in (_152_425)::env.sigtab)
in {solver = _63_174.solver; range = _63_174.range; curmodule = _63_174.curmodule; gamma = _63_174.gamma; gamma_cache = _63_174.gamma_cache; modules = _63_174.modules; expected_typ = _63_174.expected_typ; sigtab = _152_426; is_pattern = _63_174.is_pattern; instantiate_imp = _63_174.instantiate_imp; effects = _63_174.effects; generalize = _63_174.generalize; letrecs = _63_174.letrecs; top_level = _63_174.top_level; check_uvars = _63_174.check_uvars; use_eq = _63_174.use_eq; is_iface = _63_174.is_iface; admit = _63_174.admit; default_effects = _63_174.default_effects; type_of = _63_174.type_of; universe_of = _63_174.universe_of; use_bv_sorts = _63_174.use_bv_sorts}))))


let commit_mark : env  ->  env = (fun env -> (

let _63_177 = (env.solver.commit_mark "USER MARK")
in (

let sigtab = (match (env.sigtab) with
| hd::_63_181::tl -> begin
(hd)::tl
end
| _63_186 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _63_188 = env
in {solver = _63_188.solver; range = _63_188.range; curmodule = _63_188.curmodule; gamma = _63_188.gamma; gamma_cache = _63_188.gamma_cache; modules = _63_188.modules; expected_typ = _63_188.expected_typ; sigtab = sigtab; is_pattern = _63_188.is_pattern; instantiate_imp = _63_188.instantiate_imp; effects = _63_188.effects; generalize = _63_188.generalize; letrecs = _63_188.letrecs; top_level = _63_188.top_level; check_uvars = _63_188.check_uvars; use_eq = _63_188.use_eq; is_iface = _63_188.is_iface; admit = _63_188.admit; default_effects = _63_188.default_effects; type_of = _63_188.type_of; universe_of = _63_188.universe_of; use_bv_sorts = _63_188.use_bv_sorts}))))


let reset_mark : env  ->  env = (fun env -> (

let _63_191 = (env.solver.reset_mark "USER MARK")
in (

let _63_193 = env
in (let _152_431 = (FStar_List.tl env.sigtab)
in {solver = _63_193.solver; range = _63_193.range; curmodule = _63_193.curmodule; gamma = _63_193.gamma; gamma_cache = _63_193.gamma_cache; modules = _63_193.modules; expected_typ = _63_193.expected_typ; sigtab = _152_431; is_pattern = _63_193.is_pattern; instantiate_imp = _63_193.instantiate_imp; effects = _63_193.effects; generalize = _63_193.generalize; letrecs = _63_193.letrecs; top_level = _63_193.top_level; check_uvars = _63_193.check_uvars; use_eq = _63_193.use_eq; is_iface = _63_193.is_iface; admit = _63_193.admit; default_effects = _63_193.default_effects; type_of = _63_193.type_of; universe_of = _63_193.universe_of; use_bv_sorts = _63_193.use_bv_sorts}))))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(FStar_All.failwith "Too many pops")
end
| _63_203::tl -> begin
(

let _63_205 = (env.solver.pop msg)
in (

let _63_207 = env
in {solver = _63_207.solver; range = _63_207.range; curmodule = _63_207.curmodule; gamma = _63_207.gamma; gamma_cache = _63_207.gamma_cache; modules = _63_207.modules; expected_typ = _63_207.expected_typ; sigtab = tl; is_pattern = _63_207.is_pattern; instantiate_imp = _63_207.instantiate_imp; effects = _63_207.effects; generalize = _63_207.generalize; letrecs = _63_207.letrecs; top_level = _63_207.top_level; check_uvars = _63_207.check_uvars; use_eq = _63_207.use_eq; is_iface = _63_207.is_iface; admit = _63_207.admit; default_effects = _63_207.default_effects; type_of = _63_207.type_of; universe_of = _63_207.universe_of; use_bv_sorts = _63_207.use_bv_sorts}))
end))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> ((let _152_441 = (FStar_ST.read FStar_Options.debug)
in (FStar_All.pipe_right _152_441 (FStar_Util.for_some (fun x -> ((env.curmodule.FStar_Ident.str = "") || (env.curmodule.FStar_Ident.str = x)))))) && (FStar_Options.debug_level_geq l)))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Range.dummyRange) then begin
e
end else begin
(

let _63_214 = e
in {solver = _63_214.solver; range = r; curmodule = _63_214.curmodule; gamma = _63_214.gamma; gamma_cache = _63_214.gamma_cache; modules = _63_214.modules; expected_typ = _63_214.expected_typ; sigtab = _63_214.sigtab; is_pattern = _63_214.is_pattern; instantiate_imp = _63_214.instantiate_imp; effects = _63_214.effects; generalize = _63_214.generalize; letrecs = _63_214.letrecs; top_level = _63_214.top_level; check_uvars = _63_214.check_uvars; use_eq = _63_214.use_eq; is_iface = _63_214.is_iface; admit = _63_214.admit; default_effects = _63_214.default_effects; type_of = _63_214.type_of; universe_of = _63_214.universe_of; use_bv_sorts = _63_214.use_bv_sorts})
end)


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let _63_221 = env
in {solver = _63_221.solver; range = _63_221.range; curmodule = lid; gamma = _63_221.gamma; gamma_cache = _63_221.gamma_cache; modules = _63_221.modules; expected_typ = _63_221.expected_typ; sigtab = _63_221.sigtab; is_pattern = _63_221.is_pattern; instantiate_imp = _63_221.instantiate_imp; effects = _63_221.effects; generalize = _63_221.generalize; letrecs = _63_221.letrecs; top_level = _63_221.top_level; check_uvars = _63_221.check_uvars; use_eq = _63_221.use_eq; is_iface = _63_221.is_iface; admit = _63_221.admit; default_effects = _63_221.default_effects; type_of = _63_221.type_of; universe_of = _63_221.universe_of; use_bv_sorts = _63_221.use_bv_sorts}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (let _152_465 = (sigtab env)
in (FStar_Util.smap_try_find _152_465 (FStar_Ident.text_of_lid lid))))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _152_470 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _152_470)))


let new_u_univ = (fun _63_230 -> (let _152_472 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (_152_472)))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match ((ts, us)) with
| (([], t), []) -> begin
([], t)
end
| ((formals, t), _63_243) -> begin
(

let _63_245 = ()
in (

let n = ((FStar_List.length formals) - 1)
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN (((n - i), u)))))
in (let _152_479 = (FStar_Syntax_Subst.subst vs t)
in (us, _152_479)))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun _63_1 -> (match (_63_1) with
| ([], t) -> begin
([], t)
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun _63_258 -> (new_u_univ ()))))
in (inst_tscheme_with (us, t) us'))
end))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed _63_266 -> (match (_63_266) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in (

let _63_269 = if ((FStar_List.length insts) <> (FStar_List.length univs)) then begin
(let _152_495 = (let _152_494 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _152_493 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _152_492 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _152_491 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _152_494 _152_493 _152_492 _152_491)))))
in (FStar_All.failwith _152_495))
end else begin
()
end
in (let _152_496 = (inst_tscheme_with ((FStar_List.append ed.FStar_Syntax_Syntax.univs us), t) insts)
in (Prims.snd _152_496))))
end
| _63_272 -> begin
(let _152_498 = (let _152_497 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _152_497))
in (FStar_All.failwith _152_498))
end)
end))


type tri =
| Yes
| No
| Maybe


let is_Yes = (fun _discr_ -> (match (_discr_) with
| Yes (_) -> begin
true
end
| _ -> begin
false
end))


let is_No = (fun _discr_ -> (match (_discr_) with
| No (_) -> begin
true
end
| _ -> begin
false
end))


let is_Maybe = (fun _discr_ -> (match (_discr_) with
| Maybe (_) -> begin
true
end
| _ -> begin
false
end))


let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (

let cur = (current_module env)
in if (l.FStar_Ident.nsstr = cur.FStar_Ident.str) then begin
Yes
end else begin
if (FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str) then begin
(

let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (

let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (

let rec aux = (fun c l -> (match ((c, l)) with
| ([], _63_283) -> begin
Maybe
end
| (_63_286, []) -> begin
No
end
| (hd::tl, hd'::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _63_297 -> begin
No
end))
in (aux cur lns))))
end else begin
No
end
end))


let lookup_qname : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either Prims.option = (fun env lid -> (

let cur_mod = (in_cur_mod env lid)
in (

let cache = (fun t -> (

let _63_303 = (FStar_Util.smap_add env.gamma_cache lid.FStar_Ident.str t)
in Some (t)))
in (

let found = if (cur_mod <> No) then begin
(match ((FStar_Util.smap_try_find env.gamma_cache lid.FStar_Ident.str)) with
| None -> begin
(FStar_Util.find_map env.gamma (fun _63_2 -> (match (_63_2) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
(let _152_518 = (let _152_517 = (inst_tscheme t)
in FStar_Util.Inl (_152_517))
in Some (_152_518))
end else begin
None
end
end
| Binding_sig (_63_312, FStar_Syntax_Syntax.Sig_bundle (ses, _63_315, _63_317, _63_319)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _152_520 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _152_520 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
(cache (FStar_Util.Inr ((se, None))))
end else begin
None
end))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (_63_332) -> begin
Some (t)
end
| _63_335 -> begin
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
| _63_342 -> begin
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


let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| None -> begin
false
end
| Some (_63_352) -> begin
true
end))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, _63_358, _63_360, _63_362) -> begin
(add_sigelts env ses)
end
| _63_366 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _152_534 = (sigtab env)
in (FStar_Util.smap_add _152_534 l.FStar_Ident.str se))) lids))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun _63_3 -> (match (_63_3) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| _63_377 -> begin
None
end))))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun _63_4 -> (match (_63_4) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| _63_384 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((_63_388, lb::[]), _63_393, _63_395, _63_397) -> begin
(let _152_554 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_152_554))
end
| FStar_Syntax_Syntax.Sig_let ((_63_401, lbs), _63_405, _63_407, _63_409) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (_63_414) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _152_556 = (inst_tscheme (lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp))
in Some (_152_556))
end else begin
None
end
end)))
end
| _63_419 -> begin
None
end))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (match ((try_lookup_bv env bv)) with
| None -> begin
(let _152_564 = (let _152_563 = (let _152_562 = (variable_not_found bv)
in (let _152_561 = (FStar_Syntax_Syntax.range_of_bv bv)
in (_152_562, _152_561)))
in FStar_Syntax_Syntax.Error (_152_563))
in (Prims.raise _152_564))
end
| Some (t) -> begin
t
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, _63_428) -> begin
(let _152_570 = (let _152_569 = (let _152_568 = (let _152_567 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _152_567))
in (ne.FStar_Syntax_Syntax.univs, _152_568))
in (inst_tscheme _152_569))
in Some (_152_570))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, _63_435, _63_437, _63_439) -> begin
(let _152_574 = (let _152_573 = (let _152_572 = (let _152_571 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _152_571))
in (us, _152_572))
in (inst_tscheme _152_573))
in Some (_152_574))
end
| _63_443 -> begin
None
end))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match ((effect_signature se)) with
| None -> begin
None
end
| Some (_63_453, t) -> begin
Some (t)
end)
end
| _63_458 -> begin
None
end))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env lid -> (

let mapper = (fun _63_5 -> (match (_63_5) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_63_465, uvs, t, _63_469, _63_471, _63_473, _63_475, _63_477), None) -> begin
(let _152_585 = (inst_tscheme (uvs, t))
in Some (_152_585))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, _63_488), None) -> begin
if ((in_cur_mod env l) = Yes) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface) then begin
(let _152_586 = (inst_tscheme (uvs, t))
in Some (_152_586))
end else begin
None
end
end else begin
(let _152_587 = (inst_tscheme (uvs, t))
in Some (_152_587))
end
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _63_499, _63_501, _63_503, _63_505), None) -> begin
(match (tps) with
| [] -> begin
(let _152_589 = (inst_tscheme (uvs, k))
in (FStar_All.pipe_left (fun _152_588 -> Some (_152_588)) _152_589))
end
| _63_513 -> begin
(let _152_594 = (let _152_593 = (let _152_592 = (let _152_591 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _152_591))
in (uvs, _152_592))
in (inst_tscheme _152_593))
in (FStar_All.pipe_left (fun _152_590 -> Some (_152_590)) _152_594))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, _63_519, _63_521, _63_523, _63_525), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _152_596 = (inst_tscheme_with (uvs, k) us)
in (FStar_All.pipe_left (fun _152_595 -> Some (_152_595)) _152_596))
end
| _63_534 -> begin
(let _152_601 = (let _152_600 = (let _152_599 = (let _152_598 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow tps _152_598))
in (uvs, _152_599))
in (inst_tscheme_with _152_600 us))
in (FStar_All.pipe_left (fun _152_597 -> Some (_152_597)) _152_601))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (_63_538), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| _63_543 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (match ((let _152_602 = (lookup_qname env lid)
in (FStar_Util.bind_opt _152_602 mapper))) with
| Some (us, t) -> begin
Some ((us, (

let _63_549 = t
in {FStar_Syntax_Syntax.n = _63_549.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _63_549.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = _63_549.FStar_Syntax_Syntax.vars})))
end
| None -> begin
None
end)))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun _63_6 -> (match (_63_6) with
| FStar_Util.Inl (_63_556) -> begin
Some (false)
end
| FStar_Util.Inr (se, _63_560) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (_63_564, _63_566, _63_568, qs, _63_571) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (_63_575) -> begin
Some (true)
end
| _63_578 -> begin
Some (false)
end)
end))
in (match ((let _152_609 = (lookup_qname env lid)
in (FStar_Util.bind_opt _152_609 mapper))) with
| Some (b) -> begin
b
end
| None -> begin
false
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
(let _152_616 = (let _152_615 = (let _152_614 = (name_not_found l)
in (_152_614, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_152_615))
in (Prims.raise _152_616))
end
| Some (x) -> begin
x
end))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_63_591, uvs, t, _63_595, _63_597), None)) -> begin
(inst_tscheme (uvs, t))
end
| _63_605 -> begin
(let _152_623 = (let _152_622 = (let _152_621 = (name_not_found lid)
in (_152_621, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_152_622))
in (Prims.raise _152_623))
end))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_63_609, uvs, t, _63_613, _63_615, _63_617, _63_619, _63_621), None)) -> begin
(inst_tscheme (uvs, t))
end
| _63_629 -> begin
(let _152_630 = (let _152_629 = (let _152_628 = (name_not_found lid)
in (_152_628, (FStar_Ident.range_of_lid lid)))
in FStar_Syntax_Syntax.Error (_152_629))
in (Prims.raise _152_630))
end))


let lookup_definition : delta_level  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_level env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((_63_639, lbs), _63_643, _63_645, quals) when (FStar_Util.for_some (visible_at delta_level) quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_Syntax_Syntax.fv_eq_lid fv lid) then begin
(let _152_639 = (let _152_638 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (lb.FStar_Syntax_Syntax.lbunivs, _152_638))
in Some (_152_639))
end else begin
None
end)))
end
| _63_652 -> begin
None
end)
end
| _63_654 -> begin
None
end))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _152_646 = (let _152_645 = (let _152_644 = (name_not_found ftv)
in (_152_644, (FStar_Ident.range_of_lid ftv)))
in FStar_Syntax_Syntax.Error (_152_645))
in (Prims.raise _152_646))
end
| Some (k) -> begin
k
end))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun _63_664 -> (match (()) with
| () -> begin
(let _152_657 = (let _152_656 = (FStar_Util.string_of_int i)
in (let _152_655 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _152_656 _152_655)))
in (FStar_All.failwith _152_657))
end))
in (

let _63_668 = (lookup_datacon env lid)
in (match (_63_668) with
| (_63_666, t) -> begin
(match ((let _152_658 = (FStar_Syntax_Subst.compress t)
in _152_658.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _63_671) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (let _152_659 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _152_659 Prims.fst)))
end
end
| _63_676 -> begin
(fail ())
end)
end))))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_63_680, uvs, t, q, _63_685), None)) -> begin
Some (((uvs, t), q))
end
| _63_693 -> begin
None
end))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, _63_703), None)) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_7 -> (match (_63_7) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| _63_713 -> begin
false
end)))) then begin
None
end else begin
(

let insts = if (FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid) then begin
(univ)::(FStar_Syntax_Syntax.U_zero)::[]
end else begin
(univ)::[]
end
in (match ((binders, univs)) with
| ([], _63_717) -> begin
(FStar_All.failwith "Unexpected effect abbreviation with no arguments")
end
| (_63_720, _63_727::_63_724::_63_722) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(let _152_673 = (let _152_672 = (FStar_Syntax_Print.lid_to_string lid)
in (let _152_671 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _152_672 _152_671)))
in (FStar_All.failwith _152_673))
end
| _63_731 -> begin
(

let _63_735 = (let _152_675 = (let _152_674 = (FStar_Syntax_Util.arrow binders c)
in (univs, _152_674))
in (inst_tscheme_with _152_675 insts))
in (match (_63_735) with
| (_63_733, t) -> begin
(match ((let _152_676 = (FStar_Syntax_Subst.compress t)
in _152_676.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some ((binders, c))
end
| _63_741 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end))
end
end
| _63_743 -> begin
None
end))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_63_747, _63_749, _63_751, _63_753, _63_755, dcs, _63_758, _63_760), _63_764)) -> begin
dcs
end
| _63_769 -> begin
[]
end))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_63_773, _63_775, _63_777, l, _63_780, _63_782, _63_784, _63_786), _63_790)) -> begin
l
end
| _63_795 -> begin
(let _152_686 = (let _152_685 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _152_685))
in (FStar_All.failwith _152_686))
end))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (_63_799, _63_801, _63_803, _63_805, _63_807, _63_809, _63_811, _63_813), _63_817)) -> begin
true
end
| _63_822 -> begin
false
end))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (_63_826, _63_828, _63_830, _63_832, _63_834, _63_836, tags, _63_839), _63_843)) -> begin
(FStar_Util.for_some (fun _63_8 -> (match (_63_8) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| _63_855 -> begin
false
end)) tags)
end
| _63_857 -> begin
false
end))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (_63_861, _63_863, _63_865, quals, _63_868), _63_872)) -> begin
(FStar_Util.for_some (fun _63_9 -> (match (_63_9) with
| FStar_Syntax_Syntax.Projector (_63_878) -> begin
true
end
| _63_881 -> begin
false
end)) quals)
end
| _63_883 -> begin
false
end))


let interpreted_symbols : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env head -> (match ((let _152_705 = (FStar_Syntax_Util.un_uinst head)
in _152_705.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _63_889 -> begin
false
end))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _152_717 = (let _152_716 = (let _152_715 = (name_not_found l)
in (_152_715, (FStar_Ident.range_of_lid l)))
in FStar_Syntax_Syntax.Error (_152_716))
in (Prims.raise _152_717))
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
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _63_917 -> (match (_63_917) with
| (m1, m2, _63_912, _63_914, _63_916) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _152_793 = (let _152_792 = (let _152_791 = (let _152_790 = (FStar_Syntax_Print.lid_to_string l1)
in (let _152_789 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _152_790 _152_789)))
in (_152_791, env.range))
in FStar_Syntax_Syntax.Error (_152_792))
in (Prims.raise _152_793))
end
| Some (_63_920, _63_922, m3, j1, j2) -> begin
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
(let _152_808 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _152_808))
end
| Some (md) -> begin
(

let _63_943 = (inst_tscheme (md.FStar_Syntax_Syntax.univs, md.FStar_Syntax_Syntax.signature))
in (match (_63_943) with
| (_63_941, s) -> begin
(

let s = (FStar_Syntax_Subst.compress s)
in (match ((md.FStar_Syntax_Syntax.binders, s.FStar_Syntax_Syntax.n)) with
| ([], FStar_Syntax_Syntax.Tm_arrow ((a, _63_956)::(wp, _63_952)::(wlp, _63_948)::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _63_964 -> begin
(FStar_All.failwith "Impossible")
end))
end))
end))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let default_effect : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (FStar_Util.find_map env.default_effects (fun _63_971 -> (match (_63_971) with
| (l', m) -> begin
if (FStar_Ident.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, _63_976, _63_978, c, quals, r) -> begin
(match ((FStar_Util.find_map quals (fun _63_10 -> (match (_63_10) with
| FStar_Syntax_Syntax.DefaultEffect (n) -> begin
n
end
| _63_988 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(

let _63_992 = env
in {solver = _63_992.solver; range = _63_992.range; curmodule = _63_992.curmodule; gamma = _63_992.gamma; gamma_cache = _63_992.gamma_cache; modules = _63_992.modules; expected_typ = _63_992.expected_typ; sigtab = _63_992.sigtab; is_pattern = _63_992.is_pattern; instantiate_imp = _63_992.instantiate_imp; effects = _63_992.effects; generalize = _63_992.generalize; letrecs = _63_992.letrecs; top_level = _63_992.top_level; check_uvars = _63_992.check_uvars; use_eq = _63_992.use_eq; is_iface = _63_992.is_iface; admit = _63_992.admit; default_effects = ((e, l))::env.default_effects; type_of = _63_992.type_of; universe_of = _63_992.universe_of; use_bv_sorts = _63_992.use_bv_sorts})
end)
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, _63_996) -> begin
(

let effects = (

let _63_999 = env.effects
in {decls = (ne)::env.effects.decls; order = _63_999.order; joins = _63_999.joins})
in (

let _63_1002 = env
in {solver = _63_1002.solver; range = _63_1002.range; curmodule = _63_1002.curmodule; gamma = _63_1002.gamma; gamma_cache = _63_1002.gamma_cache; modules = _63_1002.modules; expected_typ = _63_1002.expected_typ; sigtab = _63_1002.sigtab; is_pattern = _63_1002.is_pattern; instantiate_imp = _63_1002.instantiate_imp; effects = effects; generalize = _63_1002.generalize; letrecs = _63_1002.letrecs; top_level = _63_1002.top_level; check_uvars = _63_1002.check_uvars; use_eq = _63_1002.use_eq; is_iface = _63_1002.is_iface; admit = _63_1002.admit; default_effects = _63_1002.default_effects; type_of = _63_1002.type_of; universe_of = _63_1002.universe_of; use_bv_sorts = _63_1002.use_bv_sorts}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, _63_1006) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _152_829 = (e1.mlift r wp1)
in (e2.mlift r _152_829)))})
in (

let mk_lift = (fun lift_t r wp1 -> (

let _63_1021 = (inst_tscheme lift_t)
in (match (_63_1021) with
| (_63_1019, lift_t) -> begin
(let _152_841 = (let _152_840 = (let _152_839 = (let _152_838 = (FStar_Syntax_Syntax.as_arg r)
in (let _152_837 = (let _152_836 = (FStar_Syntax_Syntax.as_arg wp1)
in (_152_836)::[])
in (_152_838)::_152_837))
in (lift_t, _152_839))
in FStar_Syntax_Syntax.Tm_app (_152_840))
in (FStar_Syntax_Syntax.mk _152_841 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (

let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub.FStar_Syntax_Syntax.lift)}
in (

let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (

let print_mlift = (fun l -> (

let arg = (let _152_858 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _152_858 FStar_Syntax_Syntax.Delta_constant None))
in (

let wp = (let _152_859 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _152_859 FStar_Syntax_Syntax.Delta_constant None))
in (let _152_860 = (l arg wp)
in (FStar_Syntax_Print.term_to_string _152_860)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (

let find_edge = (fun order _63_1038 -> (match (_63_1038) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _152_866 -> Some (_152_866)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _152_874 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _152_873 = (find_edge order (i, k))
in (let _152_872 = (find_edge order (k, j))
in (_152_873, _152_872)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _63_1050 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _152_874))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _152_966 = (find_edge order (i, k))
in (let _152_965 = (find_edge order (j, k))
in (_152_966, _152_965)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _63_1067, _63_1069) -> begin
if ((let _152_967 = (find_edge order (k, ub))
in (FStar_Util.is_some _152_967)) && (not ((let _152_968 = (find_edge order (ub, k))
in (FStar_Util.is_some _152_968))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _63_1073 -> begin
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

let effects = (

let _63_1082 = env.effects
in {decls = _63_1082.decls; order = order; joins = joins})
in (

let _63_1085 = env
in {solver = _63_1085.solver; range = _63_1085.range; curmodule = _63_1085.curmodule; gamma = _63_1085.gamma; gamma_cache = _63_1085.gamma_cache; modules = _63_1085.modules; expected_typ = _63_1085.expected_typ; sigtab = _63_1085.sigtab; is_pattern = _63_1085.is_pattern; instantiate_imp = _63_1085.instantiate_imp; effects = effects; generalize = _63_1085.generalize; letrecs = _63_1085.letrecs; top_level = _63_1085.top_level; check_uvars = _63_1085.check_uvars; use_eq = _63_1085.use_eq; is_iface = _63_1085.is_iface; admit = _63_1085.admit; default_effects = _63_1085.default_effects; type_of = _63_1085.type_of; universe_of = _63_1085.universe_of; use_bv_sorts = _63_1085.use_bv_sorts})))))))))))))
end
| _63_1088 -> begin
env
end))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (let _152_1017 = (

let _63_1091 = env
in (let _152_1016 = (let _152_1015 = (let _152_1014 = (let _152_1013 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_152_1013, s))
in Binding_sig (_152_1014))
in (_152_1015)::env.gamma)
in {solver = _63_1091.solver; range = _63_1091.range; curmodule = _63_1091.curmodule; gamma = _152_1016; gamma_cache = _63_1091.gamma_cache; modules = _63_1091.modules; expected_typ = _63_1091.expected_typ; sigtab = _63_1091.sigtab; is_pattern = _63_1091.is_pattern; instantiate_imp = _63_1091.instantiate_imp; effects = _63_1091.effects; generalize = _63_1091.generalize; letrecs = _63_1091.letrecs; top_level = _63_1091.top_level; check_uvars = _63_1091.check_uvars; use_eq = _63_1091.use_eq; is_iface = _63_1091.is_iface; admit = _63_1091.admit; default_effects = _63_1091.default_effects; type_of = _63_1091.type_of; universe_of = _63_1091.universe_of; use_bv_sorts = _63_1091.use_bv_sorts}))
in (build_lattice _152_1017 s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (let _152_1028 = (

let _63_1096 = env
in (let _152_1027 = (let _152_1026 = (let _152_1025 = (let _152_1024 = (FStar_Syntax_Util.lids_of_sigelt s)
in (_152_1024, s, us))
in Binding_sig_inst (_152_1025))
in (_152_1026)::env.gamma)
in {solver = _63_1096.solver; range = _63_1096.range; curmodule = _63_1096.curmodule; gamma = _152_1027; gamma_cache = _63_1096.gamma_cache; modules = _63_1096.modules; expected_typ = _63_1096.expected_typ; sigtab = _63_1096.sigtab; is_pattern = _63_1096.is_pattern; instantiate_imp = _63_1096.instantiate_imp; effects = _63_1096.effects; generalize = _63_1096.generalize; letrecs = _63_1096.letrecs; top_level = _63_1096.top_level; check_uvars = _63_1096.check_uvars; use_eq = _63_1096.use_eq; is_iface = _63_1096.is_iface; admit = _63_1096.admit; default_effects = _63_1096.default_effects; type_of = _63_1096.type_of; universe_of = _63_1096.universe_of; use_bv_sorts = _63_1096.use_bv_sorts}))
in (build_lattice _152_1028 s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let _63_1100 = env
in {solver = _63_1100.solver; range = _63_1100.range; curmodule = _63_1100.curmodule; gamma = (b)::env.gamma; gamma_cache = _63_1100.gamma_cache; modules = _63_1100.modules; expected_typ = _63_1100.expected_typ; sigtab = _63_1100.sigtab; is_pattern = _63_1100.is_pattern; instantiate_imp = _63_1100.instantiate_imp; effects = _63_1100.effects; generalize = _63_1100.generalize; letrecs = _63_1100.letrecs; top_level = _63_1100.top_level; check_uvars = _63_1100.check_uvars; use_eq = _63_1100.use_eq; is_iface = _63_1100.is_iface; admit = _63_1100.admit; default_effects = _63_1100.default_effects; type_of = _63_1100.type_of; universe_of = _63_1100.universe_of; use_bv_sorts = _63_1100.use_bv_sorts}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env _63_1110 -> (match (_63_1110) with
| (x, _63_1109) -> begin
(push_bv env x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(

let _63_1115 = ()
in (

let x = (

let _63_1117 = x
in {FStar_Syntax_Syntax.ppname = _63_1117.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_1117.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x)))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, t))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> (

let _63_1127 = (add_sigelts env m.FStar_Syntax_Syntax.exports)
in (

let _63_1129 = env
in {solver = _63_1129.solver; range = _63_1129.range; curmodule = _63_1129.curmodule; gamma = []; gamma_cache = _63_1129.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = _63_1129.sigtab; is_pattern = _63_1129.is_pattern; instantiate_imp = _63_1129.instantiate_imp; effects = _63_1129.effects; generalize = _63_1129.generalize; letrecs = _63_1129.letrecs; top_level = _63_1129.top_level; check_uvars = _63_1129.check_uvars; use_eq = _63_1129.use_eq; is_iface = _63_1129.is_iface; admit = _63_1129.admit; default_effects = _63_1129.default_effects; type_of = _63_1129.type_of; universe_of = _63_1129.universe_of; use_bv_sorts = _63_1129.use_bv_sorts})))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let _63_1137 = env
in {solver = _63_1137.solver; range = _63_1137.range; curmodule = _63_1137.curmodule; gamma = _63_1137.gamma; gamma_cache = _63_1137.gamma_cache; modules = _63_1137.modules; expected_typ = Some (t); sigtab = _63_1137.sigtab; is_pattern = _63_1137.is_pattern; instantiate_imp = _63_1137.instantiate_imp; effects = _63_1137.effects; generalize = _63_1137.generalize; letrecs = _63_1137.letrecs; top_level = _63_1137.top_level; check_uvars = _63_1137.check_uvars; use_eq = false; is_iface = _63_1137.is_iface; admit = _63_1137.admit; default_effects = _63_1137.default_effects; type_of = _63_1137.type_of; universe_of = _63_1137.universe_of; use_bv_sorts = _63_1137.use_bv_sorts}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env -> (let _152_1071 = (expected_typ env)
in ((

let _63_1144 = env
in {solver = _63_1144.solver; range = _63_1144.range; curmodule = _63_1144.curmodule; gamma = _63_1144.gamma; gamma_cache = _63_1144.gamma_cache; modules = _63_1144.modules; expected_typ = None; sigtab = _63_1144.sigtab; is_pattern = _63_1144.is_pattern; instantiate_imp = _63_1144.instantiate_imp; effects = _63_1144.effects; generalize = _63_1144.generalize; letrecs = _63_1144.letrecs; top_level = _63_1144.top_level; check_uvars = _63_1144.check_uvars; use_eq = false; is_iface = _63_1144.is_iface; admit = _63_1144.admit; default_effects = _63_1144.default_effects; type_of = _63_1144.type_of; universe_of = _63_1144.universe_of; use_bv_sorts = _63_1144.use_bv_sorts}), _152_1071)))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = if (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
(let _152_1077 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _63_11 -> (match (_63_11) with
| Binding_sig (_63_1151, se) -> begin
(se)::[]
end
| _63_1156 -> begin
[]
end))))
in (FStar_All.pipe_right _152_1077 FStar_List.rev))
end else begin
m.FStar_Syntax_Syntax.exports
end
in (

let _63_1158 = (add_sigelts env sigs)
in (

let _63_1160 = (FStar_Util.smap_clear env.gamma_cache)
in (

let _63_1162 = env
in {solver = _63_1162.solver; range = _63_1162.range; curmodule = empty_lid; gamma = []; gamma_cache = _63_1162.gamma_cache; modules = (m)::env.modules; expected_typ = _63_1162.expected_typ; sigtab = _63_1162.sigtab; is_pattern = _63_1162.is_pattern; instantiate_imp = _63_1162.instantiate_imp; effects = _63_1162.effects; generalize = _63_1162.generalize; letrecs = _63_1162.letrecs; top_level = _63_1162.top_level; check_uvars = _63_1162.check_uvars; use_eq = _63_1162.use_eq; is_iface = _63_1162.is_iface; admit = _63_1162.admit; default_effects = _63_1162.default_effects; type_of = _63_1162.type_of; universe_of = _63_1162.universe_of; use_bv_sorts = _63_1162.use_bv_sorts}))))))


let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (

let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| Binding_univ (_63_1175)::tl -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _152_1089 = (let _152_1088 = (FStar_Syntax_Free.uvars t)
in (ext out _152_1088))
in (aux _152_1089 tl))
end
| (Binding_sig (_)::_) | (Binding_sig_inst (_)::_) -> begin
out
end))
in (aux no_uvs env.gamma)))))


let univ_vars : env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun env -> (

let no_univs = FStar_Syntax_Syntax.no_universe_uvars
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_sig_inst (_)::tl) | (Binding_univ (_)::tl) -> begin
(aux out tl)
end
| (Binding_lid (_, (_, t))::tl) | (Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})::tl) -> begin
(let _152_1101 = (let _152_1100 = (FStar_Syntax_Free.univs t)
in (ext out _152_1100))
in (aux _152_1101 tl))
end
| Binding_sig (_63_1245)::_63_1243 -> begin
out
end))
in (aux no_univs env.gamma)))))


let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _63_12 -> (match (_63_12) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _152_1108 = (let _152_1107 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _152_1107 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _152_1108 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys _63_13 -> (match (_63_13) with
| Binding_sig (lids, _63_1277) -> begin
(FStar_List.append lids keys)
end
| _63_1281 -> begin
keys
end)) [] env.gamma)
in (let _152_1132 = (sigtab env)
in (FStar_Util.smap_fold _152_1132 (fun _63_1283 v keys -> (let _152_1131 = (FStar_Syntax_Util.lids_of_sigelt v)
in (FStar_List.append _152_1131 keys))) keys))))


let dummy_solver : solver_t = {init = (fun _63_1287 -> ()); push = (fun _63_1289 -> ()); pop = (fun _63_1291 -> ()); mark = (fun _63_1293 -> ()); reset_mark = (fun _63_1295 -> ()); commit_mark = (fun _63_1297 -> ()); encode_modul = (fun _63_1299 _63_1301 -> ()); encode_sig = (fun _63_1303 _63_1305 -> ()); solve = (fun _63_1307 _63_1309 _63_1311 -> ()); is_trivial = (fun _63_1313 _63_1315 -> false); finish = (fun _63_1317 -> ()); refresh = (fun _63_1318 -> ())}


let no_solver_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * guard_t))  ->  env = (fun tc -> (let _152_1168 = (FStar_Ident.lid_of_path (("dummy")::[]) FStar_Range.dummyRange)
in (initial_env tc dummy_solver _152_1168)))




