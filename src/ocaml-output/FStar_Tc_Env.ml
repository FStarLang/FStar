
open Prims
# 28 "FStar.Tc.Env.fst"
type binding =
| Binding_var of (FStar_Absyn_Syntax.bvvdef * FStar_Absyn_Syntax.typ)
| Binding_typ of (FStar_Absyn_Syntax.btvdef * FStar_Absyn_Syntax.knd)
| Binding_lid of (FStar_Ident.lident * FStar_Absyn_Syntax.typ)
| Binding_sig of FStar_Absyn_Syntax.sigelt

# 29 "FStar.Tc.Env.fst"
let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "FStar.Tc.Env.fst"
let is_Binding_typ = (fun _discr_ -> (match (_discr_) with
| Binding_typ (_) -> begin
true
end
| _ -> begin
false
end))

# 31 "FStar.Tc.Env.fst"
let is_Binding_lid = (fun _discr_ -> (match (_discr_) with
| Binding_lid (_) -> begin
true
end
| _ -> begin
false
end))

# 32 "FStar.Tc.Env.fst"
let is_Binding_sig = (fun _discr_ -> (match (_discr_) with
| Binding_sig (_) -> begin
true
end
| _ -> begin
false
end))

# 29 "FStar.Tc.Env.fst"
let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_30_16) -> begin
_30_16
end))

# 30 "FStar.Tc.Env.fst"
let ___Binding_typ____0 = (fun projectee -> (match (projectee) with
| Binding_typ (_30_19) -> begin
_30_19
end))

# 31 "FStar.Tc.Env.fst"
let ___Binding_lid____0 = (fun projectee -> (match (projectee) with
| Binding_lid (_30_22) -> begin
_30_22
end))

# 32 "FStar.Tc.Env.fst"
let ___Binding_sig____0 = (fun projectee -> (match (projectee) with
| Binding_sig (_30_25) -> begin
_30_25
end))

# 34 "FStar.Tc.Env.fst"
type sigtable =
FStar_Absyn_Syntax.sigelt FStar_Util.smap

# 35 "FStar.Tc.Env.fst"
let default_table_size : Prims.int = 200

# 36 "FStar.Tc.Env.fst"
let strlid_of_sigelt : FStar_Absyn_Syntax.sigelt  ->  Prims.string Prims.option = (fun se -> (match ((FStar_Absyn_Util.lid_of_sigelt se)) with
| None -> begin
None
end
| Some (l) -> begin
Some ((FStar_Ident.text_of_lid l))
end))

# 39 "FStar.Tc.Env.fst"
let signature_to_sigtables : FStar_Absyn_Syntax.sigelt Prims.list  ->  FStar_Absyn_Syntax.sigelt FStar_Util.smap = (fun s -> (
# 40 "FStar.Tc.Env.fst"
let ht = (FStar_Util.smap_create default_table_size)
in (
# 41 "FStar.Tc.Env.fst"
let _30_35 = (FStar_List.iter (fun se -> (
# 42 "FStar.Tc.Env.fst"
let lids = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (FStar_Util.smap_add ht l.FStar_Ident.str se)) lids))) s)
in ht)))

# 46 "FStar.Tc.Env.fst"
let modules_to_sigtables = (fun mods -> (let _109_65 = (FStar_List.collect (fun _30_41 -> (match (_30_41) with
| (_30_39, m) -> begin
m.FStar_Absyn_Syntax.declarations
end)) mods)
in (signature_to_sigtables _109_65)))

# 49 "FStar.Tc.Env.fst"
type level =
| Expr
| Type
| Kind

# 50 "FStar.Tc.Env.fst"
let is_Expr = (fun _discr_ -> (match (_discr_) with
| Expr (_) -> begin
true
end
| _ -> begin
false
end))

# 51 "FStar.Tc.Env.fst"
let is_Type = (fun _discr_ -> (match (_discr_) with
| Type (_) -> begin
true
end
| _ -> begin
false
end))

# 52 "FStar.Tc.Env.fst"
let is_Kind = (fun _discr_ -> (match (_discr_) with
| Kind (_) -> begin
true
end
| _ -> begin
false
end))

# 54 "FStar.Tc.Env.fst"
type mlift =
FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ

# 55 "FStar.Tc.Env.fst"
type edge =
{msource : FStar_Ident.lident; mtarget : FStar_Ident.lident; mlift : mlift}

# 55 "FStar.Tc.Env.fst"
let is_Mkedge : edge  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkedge"))))

# 60 "FStar.Tc.Env.fst"
type effects =
{decls : FStar_Absyn_Syntax.eff_decl Prims.list; order : edge Prims.list; joins : (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list}

# 60 "FStar.Tc.Env.fst"
let is_Mkeffects : effects  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeffects"))))

# 66 "FStar.Tc.Env.fst"
type env =
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; modules : FStar_Absyn_Syntax.modul Prims.list; expected_typ : FStar_Absyn_Syntax.typ Prims.option; level : level; sigtab : sigtable Prims.list; is_pattern : Prims.bool; instantiate_targs : Prims.bool; instantiate_vargs : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; default_effects : (FStar_Ident.lident * FStar_Ident.lident) Prims.list} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Absyn_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit; solve : env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}

# 66 "FStar.Tc.Env.fst"
let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

# 88 "FStar.Tc.Env.fst"
let is_Mksolver_t : solver_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksolver_t"))))

# 160 "FStar.Tc.Env.fst"
let bound_vars : env  ->  (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either Prims.list = (fun env -> (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _30_1 -> (match (_30_1) with
| Binding_typ (a, k) -> begin
(let _109_291 = (FStar_All.pipe_left (fun _109_290 -> FStar_Util.Inl (_109_290)) (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_109_291)::[])
end
| Binding_var (x, t) -> begin
(let _109_293 = (FStar_All.pipe_left (fun _109_292 -> FStar_Util.Inr (_109_292)) (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_109_293)::[])
end
| Binding_lid (_30_96) -> begin
[]
end
| Binding_sig (_30_99) -> begin
[]
end)))))

# 167 "FStar.Tc.Env.fst"
let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Absyn_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Absyn_Syntax.name l))))))

# 170 "FStar.Tc.Env.fst"
let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> ((let _109_304 = (FStar_ST.read FStar_Options.debug)
in (FStar_All.pipe_right _109_304 (FStar_Util.for_some (fun x -> (env.curmodule.FStar_Ident.str = x))))) && (FStar_Options.debug_level_geq l)))

# 173 "FStar.Tc.Env.fst"
let show : env  ->  Prims.bool = (fun env -> (let _109_308 = (FStar_ST.read FStar_Options.show_signatures)
in (FStar_All.pipe_right _109_308 (FStar_Util.for_some (fun x -> (env.curmodule.FStar_Ident.str = x))))))

# 175 "FStar.Tc.Env.fst"
let new_sigtab = (fun _30_109 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))

# 176 "FStar.Tc.Env.fst"
let sigtab : env  ->  sigtable = (fun env -> (FStar_List.hd env.sigtab))

# 177 "FStar.Tc.Env.fst"
let push : env  ->  Prims.string  ->  env = (fun env msg -> (
# 178 "FStar.Tc.Env.fst"
let _30_113 = (env.solver.push msg)
in (
# 179 "FStar.Tc.Env.fst"
let _30_115 = env
in (let _109_318 = (let _109_317 = (let _109_316 = (sigtab env)
in (FStar_Util.smap_copy _109_316))
in (_109_317)::env.sigtab)
in {solver = _30_115.solver; range = _30_115.range; curmodule = _30_115.curmodule; gamma = _30_115.gamma; modules = _30_115.modules; expected_typ = _30_115.expected_typ; level = _30_115.level; sigtab = _109_318; is_pattern = _30_115.is_pattern; instantiate_targs = _30_115.instantiate_targs; instantiate_vargs = _30_115.instantiate_vargs; effects = _30_115.effects; generalize = _30_115.generalize; letrecs = _30_115.letrecs; top_level = _30_115.top_level; check_uvars = _30_115.check_uvars; use_eq = _30_115.use_eq; is_iface = _30_115.is_iface; admit = _30_115.admit; default_effects = _30_115.default_effects}))))

# 180 "FStar.Tc.Env.fst"
let mark : env  ->  env = (fun env -> (
# 181 "FStar.Tc.Env.fst"
let _30_118 = (env.solver.mark "USER MARK")
in (
# 182 "FStar.Tc.Env.fst"
let _30_120 = env
in (let _109_323 = (let _109_322 = (let _109_321 = (sigtab env)
in (FStar_Util.smap_copy _109_321))
in (_109_322)::env.sigtab)
in {solver = _30_120.solver; range = _30_120.range; curmodule = _30_120.curmodule; gamma = _30_120.gamma; modules = _30_120.modules; expected_typ = _30_120.expected_typ; level = _30_120.level; sigtab = _109_323; is_pattern = _30_120.is_pattern; instantiate_targs = _30_120.instantiate_targs; instantiate_vargs = _30_120.instantiate_vargs; effects = _30_120.effects; generalize = _30_120.generalize; letrecs = _30_120.letrecs; top_level = _30_120.top_level; check_uvars = _30_120.check_uvars; use_eq = _30_120.use_eq; is_iface = _30_120.is_iface; admit = _30_120.admit; default_effects = _30_120.default_effects}))))

# 183 "FStar.Tc.Env.fst"
let commit_mark : env  ->  env = (fun env -> (
# 184 "FStar.Tc.Env.fst"
let _30_123 = (env.solver.commit_mark "USER MARK")
in (
# 185 "FStar.Tc.Env.fst"
let sigtab = (match (env.sigtab) with
| hd::_30_127::tl -> begin
(hd)::tl
end
| _30_132 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 188 "FStar.Tc.Env.fst"
let _30_134 = env
in {solver = _30_134.solver; range = _30_134.range; curmodule = _30_134.curmodule; gamma = _30_134.gamma; modules = _30_134.modules; expected_typ = _30_134.expected_typ; level = _30_134.level; sigtab = sigtab; is_pattern = _30_134.is_pattern; instantiate_targs = _30_134.instantiate_targs; instantiate_vargs = _30_134.instantiate_vargs; effects = _30_134.effects; generalize = _30_134.generalize; letrecs = _30_134.letrecs; top_level = _30_134.top_level; check_uvars = _30_134.check_uvars; use_eq = _30_134.use_eq; is_iface = _30_134.is_iface; admit = _30_134.admit; default_effects = _30_134.default_effects}))))

# 189 "FStar.Tc.Env.fst"
let reset_mark : env  ->  env = (fun env -> (
# 190 "FStar.Tc.Env.fst"
let _30_137 = (env.solver.reset_mark "USER MARK")
in (
# 191 "FStar.Tc.Env.fst"
let _30_139 = env
in (let _109_328 = (FStar_List.tl env.sigtab)
in {solver = _30_139.solver; range = _30_139.range; curmodule = _30_139.curmodule; gamma = _30_139.gamma; modules = _30_139.modules; expected_typ = _30_139.expected_typ; level = _30_139.level; sigtab = _109_328; is_pattern = _30_139.is_pattern; instantiate_targs = _30_139.instantiate_targs; instantiate_vargs = _30_139.instantiate_vargs; effects = _30_139.effects; generalize = _30_139.generalize; letrecs = _30_139.letrecs; top_level = _30_139.top_level; check_uvars = _30_139.check_uvars; use_eq = _30_139.use_eq; is_iface = _30_139.is_iface; admit = _30_139.admit; default_effects = _30_139.default_effects}))))

# 192 "FStar.Tc.Env.fst"
let pop : env  ->  Prims.string  ->  env = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(FStar_All.failwith "Too many pops")
end
| _30_149::tl -> begin
(
# 196 "FStar.Tc.Env.fst"
let _30_151 = (env.solver.pop msg)
in (
# 197 "FStar.Tc.Env.fst"
let _30_153 = env
in {solver = _30_153.solver; range = _30_153.range; curmodule = _30_153.curmodule; gamma = _30_153.gamma; modules = _30_153.modules; expected_typ = _30_153.expected_typ; level = _30_153.level; sigtab = tl; is_pattern = _30_153.is_pattern; instantiate_targs = _30_153.instantiate_targs; instantiate_vargs = _30_153.instantiate_vargs; effects = _30_153.effects; generalize = _30_153.generalize; letrecs = _30_153.letrecs; top_level = _30_153.top_level; check_uvars = _30_153.check_uvars; use_eq = _30_153.use_eq; is_iface = _30_153.is_iface; admit = _30_153.admit; default_effects = _30_153.default_effects}))
end))

# 199 "FStar.Tc.Env.fst"
let initial_env : solver_t  ->  FStar_Ident.lident  ->  env = (fun solver module_lid -> (let _109_338 = (let _109_337 = (new_sigtab ())
in (_109_337)::[])
in {solver = solver; range = FStar_Absyn_Syntax.dummyRange; curmodule = module_lid; gamma = []; modules = []; expected_typ = None; level = Expr; sigtab = _109_338; is_pattern = false; instantiate_targs = true; instantiate_vargs = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = true; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []}))

# 223 "FStar.Tc.Env.fst"
let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Absyn_Syntax.mname l)))))

# 226 "FStar.Tc.Env.fst"
let name_not_found : FStar_Absyn_Syntax.lident  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))

# 229 "FStar.Tc.Env.fst"
let variable_not_found = (fun v -> (let _109_347 = (FStar_Absyn_Print.strBvd v)
in (FStar_Util.format1 "Variable \"%s\" not found" _109_347)))

# 232 "FStar.Tc.Env.fst"
let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _109_354 = (let _109_353 = (let _109_352 = (name_not_found l)
in (_109_352, (FStar_Ident.range_of_lid l)))
in FStar_Absyn_Syntax.Error (_109_353))
in (Prims.raise _109_354))
end
| Some (md) -> begin
md
end))

# 237 "FStar.Tc.Env.fst"
let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
(l1, (fun t wp -> wp), (fun t wp -> wp))
end else begin
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _30_182 -> (match (_30_182) with
| (m1, m2, _30_177, _30_179, _30_181) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _109_410 = (let _109_409 = (let _109_408 = (let _109_407 = (FStar_Absyn_Print.sli l1)
in (let _109_406 = (FStar_Absyn_Print.sli l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _109_407 _109_406)))
in (_109_408, env.range))
in FStar_Absyn_Syntax.Error (_109_409))
in (Prims.raise _109_410))
end
| Some (_30_185, _30_187, m3, j1, j2) -> begin
(m3, j1, j2)
end)
end)

# 244 "FStar.Tc.Env.fst"
let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge Prims.option = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end else begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end)

# 249 "FStar.Tc.Env.fst"
let wp_sig_aux : FStar_Absyn_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) = (fun decls m -> (match ((FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Absyn_Syntax.mname m))))) with
| None -> begin
(let _109_425 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _109_425))
end
| Some (md) -> begin
(match (md.FStar_Absyn_Syntax.signature.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow ((FStar_Util.Inl (a), _30_218)::(FStar_Util.Inl (wp), _30_213)::(FStar_Util.Inl (wlp), _30_208)::[], {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_effect; FStar_Absyn_Syntax.tk = _30_228; FStar_Absyn_Syntax.pos = _30_226; FStar_Absyn_Syntax.fvs = _30_224; FStar_Absyn_Syntax.uvs = _30_222}) -> begin
(a, wp.FStar_Absyn_Syntax.sort)
end
| _30_234 -> begin
(FStar_All.failwith "Impossible")
end)
end))

# 257 "FStar.Tc.Env.fst"
let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.btvar * FStar_Absyn_Syntax.knd) = (fun env m -> (wp_sig_aux env.effects.decls m))

# 259 "FStar.Tc.Env.fst"
let default_effect : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (FStar_Util.find_map env.default_effects (fun _30_241 -> (match (_30_241) with
| (l', m) -> begin
if (FStar_Ident.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))

# 261 "FStar.Tc.Env.fst"
let build_lattice : env  ->  FStar_Absyn_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Absyn_Syntax.Sig_effect_abbrev (l, _30_246, c, quals, r) -> begin
(match ((FStar_Util.find_map quals (fun _30_2 -> (match (_30_2) with
| FStar_Absyn_Syntax.DefaultEffect (n) -> begin
n
end
| _30_256 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(
# 265 "FStar.Tc.Env.fst"
let _30_260 = env
in {solver = _30_260.solver; range = _30_260.range; curmodule = _30_260.curmodule; gamma = _30_260.gamma; modules = _30_260.modules; expected_typ = _30_260.expected_typ; level = _30_260.level; sigtab = _30_260.sigtab; is_pattern = _30_260.is_pattern; instantiate_targs = _30_260.instantiate_targs; instantiate_vargs = _30_260.instantiate_vargs; effects = _30_260.effects; generalize = _30_260.generalize; letrecs = _30_260.letrecs; top_level = _30_260.top_level; check_uvars = _30_260.check_uvars; use_eq = _30_260.use_eq; is_iface = _30_260.is_iface; admit = _30_260.admit; default_effects = ((e, l))::env.default_effects})
end)
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, _30_264) -> begin
(
# 268 "FStar.Tc.Env.fst"
let effects = (
# 268 "FStar.Tc.Env.fst"
let _30_267 = env.effects
in {decls = (ne)::env.effects.decls; order = _30_267.order; joins = _30_267.joins})
in (
# 269 "FStar.Tc.Env.fst"
let _30_270 = env
in {solver = _30_270.solver; range = _30_270.range; curmodule = _30_270.curmodule; gamma = _30_270.gamma; modules = _30_270.modules; expected_typ = _30_270.expected_typ; level = _30_270.level; sigtab = _30_270.sigtab; is_pattern = _30_270.is_pattern; instantiate_targs = _30_270.instantiate_targs; instantiate_vargs = _30_270.instantiate_vargs; effects = effects; generalize = _30_270.generalize; letrecs = _30_270.letrecs; top_level = _30_270.top_level; check_uvars = _30_270.check_uvars; use_eq = _30_270.use_eq; is_iface = _30_270.is_iface; admit = _30_270.admit; default_effects = _30_270.default_effects}))
end
| FStar_Absyn_Syntax.Sig_sub_effect (sub, _30_274) -> begin
(
# 272 "FStar.Tc.Env.fst"
let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _109_446 = (e1.mlift r wp1)
in (e2.mlift r _109_446)))})
in (
# 277 "FStar.Tc.Env.fst"
let mk_lift = (fun lift_t r wp1 -> (let _109_457 = (let _109_456 = (let _109_455 = (FStar_Absyn_Syntax.targ r)
in (let _109_454 = (let _109_453 = (FStar_Absyn_Syntax.targ wp1)
in (_109_453)::[])
in (_109_455)::_109_454))
in (lift_t, _109_456))
in (FStar_Absyn_Syntax.mk_Typ_app _109_457 None wp1.FStar_Absyn_Syntax.pos)))
in (
# 279 "FStar.Tc.Env.fst"
let edge = {msource = sub.FStar_Absyn_Syntax.source; mtarget = sub.FStar_Absyn_Syntax.target; mlift = (mk_lift sub.FStar_Absyn_Syntax.lift)}
in (
# 283 "FStar.Tc.Env.fst"
let id_edge = (fun l -> {msource = sub.FStar_Absyn_Syntax.source; mtarget = sub.FStar_Absyn_Syntax.target; mlift = (fun t wp -> wp)})
in (
# 288 "FStar.Tc.Env.fst"
let print_mlift = (fun l -> (
# 289 "FStar.Tc.Env.fst"
let arg = (let _109_474 = (FStar_Absyn_Syntax.lid_of_path (("ARG")::[]) FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Util.ftv _109_474 FStar_Absyn_Syntax.mk_Kind_type))
in (
# 290 "FStar.Tc.Env.fst"
let wp = (let _109_475 = (FStar_Absyn_Syntax.lid_of_path (("WP")::[]) FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Util.ftv _109_475 FStar_Absyn_Syntax.mk_Kind_unknown))
in (let _109_476 = (l arg wp)
in (FStar_Absyn_Print.typ_to_string _109_476)))))
in (
# 292 "FStar.Tc.Env.fst"
let order = (edge)::env.effects.order
in (
# 294 "FStar.Tc.Env.fst"
let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Absyn_Syntax.mname)))
in (
# 296 "FStar.Tc.Env.fst"
let find_edge = (fun order _30_302 -> (match (_30_302) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _109_482 -> Some (_109_482)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (
# 305 "FStar.Tc.Env.fst"
let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _109_490 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _109_489 = (find_edge order (i, k))
in (let _109_488 = (find_edge order (k, j))
in (_109_489, _109_488)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _30_314 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _109_490))) order))
in (
# 316 "FStar.Tc.Env.fst"
let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (
# 318 "FStar.Tc.Env.fst"
let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (
# 321 "FStar.Tc.Env.fst"
let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _109_498 = (find_edge order (i, k))
in (let _109_497 = (find_edge order (j, k))
in (_109_498, _109_497)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _30_331, _30_333) -> begin
if ((let _109_499 = (find_edge order (k, ub))
in (FStar_Util.is_some _109_499)) && (not ((let _109_500 = (find_edge order (ub, k))
in (FStar_Util.is_some _109_500))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _30_337 -> begin
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
# 338 "FStar.Tc.Env.fst"
let effects = (
# 338 "FStar.Tc.Env.fst"
let _30_346 = env.effects
in {decls = _30_346.decls; order = order; joins = joins})
in (
# 341 "FStar.Tc.Env.fst"
let _30_349 = env
in {solver = _30_349.solver; range = _30_349.range; curmodule = _30_349.curmodule; gamma = _30_349.gamma; modules = _30_349.modules; expected_typ = _30_349.expected_typ; level = _30_349.level; sigtab = _30_349.sigtab; is_pattern = _30_349.is_pattern; instantiate_targs = _30_349.instantiate_targs; instantiate_vargs = _30_349.instantiate_vargs; effects = effects; generalize = _30_349.generalize; letrecs = _30_349.letrecs; top_level = _30_349.top_level; check_uvars = _30_349.check_uvars; use_eq = _30_349.use_eq; is_iface = _30_349.is_iface; admit = _30_349.admit; default_effects = _30_349.default_effects})))))))))))))
end
| _30_352 -> begin
env
end))

# 346 "FStar.Tc.Env.fst"
let rec add_sigelt : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Absyn_Syntax.Sig_bundle (ses, _30_357, _30_359, _30_361) -> begin
(add_sigelts env ses)
end
| _30_365 -> begin
(
# 349 "FStar.Tc.Env.fst"
let lids = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _109_508 = (sigtab env)
in (FStar_Util.smap_add _109_508 l.FStar_Ident.str se))) lids))
end))
and add_sigelts : env  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))

# 355 "FStar.Tc.Env.fst"
let empty_lid : FStar_Absyn_Syntax.lident = (let _109_512 = (let _109_511 = (FStar_Absyn_Syntax.id_of_text "")
in (_109_511)::[])
in (FStar_Absyn_Syntax.lid_of_ids _109_512))

# 357 "FStar.Tc.Env.fst"
let finish_module : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env m -> (
# 358 "FStar.Tc.Env.fst"
let sigs = if (FStar_Ident.lid_equals m.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid) then begin
(FStar_All.pipe_right env.gamma (FStar_List.collect (fun _30_3 -> (match (_30_3) with
| Binding_sig (se) -> begin
(se)::[]
end
| _30_376 -> begin
[]
end))))
end else begin
m.FStar_Absyn_Syntax.exports
end
in (
# 364 "FStar.Tc.Env.fst"
let _30_378 = (add_sigelts env sigs)
in (
# 365 "FStar.Tc.Env.fst"
let _30_380 = env
in {solver = _30_380.solver; range = _30_380.range; curmodule = empty_lid; gamma = []; modules = (m)::env.modules; expected_typ = _30_380.expected_typ; level = _30_380.level; sigtab = _30_380.sigtab; is_pattern = _30_380.is_pattern; instantiate_targs = _30_380.instantiate_targs; instantiate_vargs = _30_380.instantiate_vargs; effects = _30_380.effects; generalize = _30_380.generalize; letrecs = _30_380.letrecs; top_level = _30_380.top_level; check_uvars = _30_380.check_uvars; use_eq = _30_380.use_eq; is_iface = _30_380.is_iface; admit = _30_380.admit; default_effects = _30_380.default_effects}))))

# 371 "FStar.Tc.Env.fst"
let set_level : env  ->  level  ->  env = (fun env level -> (
# 371 "FStar.Tc.Env.fst"
let _30_384 = env
in {solver = _30_384.solver; range = _30_384.range; curmodule = _30_384.curmodule; gamma = _30_384.gamma; modules = _30_384.modules; expected_typ = _30_384.expected_typ; level = level; sigtab = _30_384.sigtab; is_pattern = _30_384.is_pattern; instantiate_targs = _30_384.instantiate_targs; instantiate_vargs = _30_384.instantiate_vargs; effects = _30_384.effects; generalize = _30_384.generalize; letrecs = _30_384.letrecs; top_level = _30_384.top_level; check_uvars = _30_384.check_uvars; use_eq = _30_384.use_eq; is_iface = _30_384.is_iface; admit = _30_384.admit; default_effects = _30_384.default_effects}))

# 372 "FStar.Tc.Env.fst"
let is_level : env  ->  level  ->  Prims.bool = (fun env level -> (env.level = level))

# 373 "FStar.Tc.Env.fst"
let modules : env  ->  FStar_Absyn_Syntax.modul Prims.list = (fun env -> env.modules)

# 374 "FStar.Tc.Env.fst"
let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)

# 375 "FStar.Tc.Env.fst"
let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (
# 375 "FStar.Tc.Env.fst"
let _30_392 = env
in {solver = _30_392.solver; range = _30_392.range; curmodule = lid; gamma = _30_392.gamma; modules = _30_392.modules; expected_typ = _30_392.expected_typ; level = _30_392.level; sigtab = _30_392.sigtab; is_pattern = _30_392.is_pattern; instantiate_targs = _30_392.instantiate_targs; instantiate_vargs = _30_392.instantiate_vargs; effects = _30_392.effects; generalize = _30_392.generalize; letrecs = _30_392.letrecs; top_level = _30_392.top_level; check_uvars = _30_392.check_uvars; use_eq = _30_392.use_eq; is_iface = _30_392.is_iface; admit = _30_392.admit; default_effects = _30_392.default_effects}))

# 376 "FStar.Tc.Env.fst"
let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Absyn_Syntax.dummyRange) then begin
e
end else begin
(
# 376 "FStar.Tc.Env.fst"
let _30_396 = e
in {solver = _30_396.solver; range = r; curmodule = _30_396.curmodule; gamma = _30_396.gamma; modules = _30_396.modules; expected_typ = _30_396.expected_typ; level = _30_396.level; sigtab = _30_396.sigtab; is_pattern = _30_396.is_pattern; instantiate_targs = _30_396.instantiate_targs; instantiate_vargs = _30_396.instantiate_vargs; effects = _30_396.effects; generalize = _30_396.generalize; letrecs = _30_396.letrecs; top_level = _30_396.top_level; check_uvars = _30_396.check_uvars; use_eq = _30_396.use_eq; is_iface = _30_396.is_iface; admit = _30_396.admit; default_effects = _30_396.default_effects})
end)

# 377 "FStar.Tc.Env.fst"
let get_range : env  ->  FStar_Range.range = (fun e -> e.range)

# 378 "FStar.Tc.Env.fst"
let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.sigelt Prims.option = (fun env lid -> (let _109_544 = (sigtab env)
in (FStar_Util.smap_try_find _109_544 (FStar_Ident.text_of_lid lid))))

# 380 "FStar.Tc.Env.fst"
let lookup_bvvdef : env  ->  FStar_Absyn_Syntax.bvvdef  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env bvvd -> (FStar_Util.find_map env.gamma (fun _30_4 -> (match (_30_4) with
| Binding_var (id, t) when (FStar_Absyn_Util.bvd_eq id bvvd) -> begin
Some (t)
end
| _30_409 -> begin
None
end))))

# 385 "FStar.Tc.Env.fst"
let lookup_bvar : env  ->  FStar_Absyn_Syntax.bvvar  ->  FStar_Absyn_Syntax.typ = (fun env bv -> (match ((lookup_bvvdef env bv.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _109_556 = (let _109_555 = (let _109_554 = (variable_not_found bv.FStar_Absyn_Syntax.v)
in (_109_554, (FStar_Absyn_Util.range_of_bvd bv.FStar_Absyn_Syntax.v)))
in FStar_Absyn_Syntax.Error (_109_555))
in (Prims.raise _109_556))
end
| Some (t) -> begin
t
end))

# 390 "FStar.Tc.Env.fst"
let in_cur_mod : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 391 "FStar.Tc.Env.fst"
let cur = (current_module env)
in if (l.FStar_Ident.nsstr = cur.FStar_Ident.str) then begin
true
end else begin
if (FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str) then begin
(
# 394 "FStar.Tc.Env.fst"
let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (
# 395 "FStar.Tc.Env.fst"
let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (
# 396 "FStar.Tc.Env.fst"
let rec aux = (fun c l -> (match ((c, l)) with
| ([], _30_425) -> begin
true
end
| (_30_428, []) -> begin
false
end
| (hd::tl, hd'::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _30_439 -> begin
false
end))
in (aux cur lns))))
end else begin
false
end
end))

# 404 "FStar.Tc.Env.fst"
let lookup_qname : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.sigelt) FStar_Util.either Prims.option = (fun env lid -> (
# 405 "FStar.Tc.Env.fst"
let cur_mod = (in_cur_mod env lid)
in (
# 406 "FStar.Tc.Env.fst"
let found = if cur_mod then begin
(FStar_Util.find_map env.gamma (fun _30_5 -> (match (_30_5) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
Some (FStar_Util.Inl (t))
end else begin
None
end
end
| Binding_sig (FStar_Absyn_Syntax.Sig_bundle (ses, _30_450, _30_452, _30_454)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _109_571 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _109_571 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
Some (FStar_Util.Inr (se))
end else begin
None
end))
end
| Binding_sig (s) -> begin
(
# 415 "FStar.Tc.Env.fst"
let lids = (FStar_Absyn_Util.lids_of_sigelt s)
in if (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals lid))) then begin
Some (FStar_Util.Inr (s))
end else begin
None
end)
end
| _30_463 -> begin
None
end)))
end else begin
None
end
in if (FStar_Util.is_some found) then begin
found
end else begin
if ((not (cur_mod)) || (has_interface env env.curmodule)) then begin
(match ((find_in_sigtab env lid)) with
| Some (se) -> begin
Some (FStar_Util.Inr (se))
end
| None -> begin
None
end)
end else begin
None
end
end)))

# 427 "FStar.Tc.Env.fst"
let lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_30_471, t, (_30_474, tps, _30_477), _30_480, _30_482, _30_484))) -> begin
(let _109_577 = (FStar_List.map (fun _30_492 -> (match (_30_492) with
| (x, _30_491) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit (true)))
end)) tps)
in (FStar_Absyn_Util.close_typ _109_577 t))
end
| _30_494 -> begin
(let _109_580 = (let _109_579 = (let _109_578 = (name_not_found lid)
in (_109_578, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_109_579))
in (Prims.raise _109_580))
end))

# 433 "FStar.Tc.Env.fst"
let lookup_kind_abbrev : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_kind_abbrev (l, binders, k, _30_501))) -> begin
(l, binders, k)
end
| _30_507 -> begin
(let _109_587 = (let _109_586 = (let _109_585 = (name_not_found lid)
in (_109_585, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_109_586))
in (Prims.raise _109_587))
end))

# 438 "FStar.Tc.Env.fst"
let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (
# 439 "FStar.Tc.Env.fst"
let fail = (fun _30_512 -> (match (()) with
| () -> begin
(let _109_598 = (let _109_597 = (FStar_Util.string_of_int i)
in (let _109_596 = (FStar_Absyn_Print.sli lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _109_597 _109_596)))
in (FStar_All.failwith _109_598))
end))
in (
# 440 "FStar.Tc.Env.fst"
let t = (lookup_datacon env lid)
in (match ((let _109_599 = (FStar_Absyn_Util.compress_typ t)
in _109_599.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, _30_516) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(
# 445 "FStar.Tc.Env.fst"
let b = (FStar_List.nth binders i)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _109_600 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (FStar_All.pipe_right _109_600 Prims.fst))
end
| FStar_Util.Inr (x) -> begin
(let _109_601 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (FStar_All.pipe_right _109_601 Prims.fst))
end))
end
end
| _30_525 -> begin
(fail ())
end))))

# 452 "FStar.Tc.Env.fst"
let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_30_529, t, q, _30_533))) -> begin
Some ((t, q))
end
| _30_539 -> begin
None
end))

# 457 "FStar.Tc.Env.fst"
let lookup_val_decl : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_30_543, t, _30_546, _30_548))) -> begin
t
end
| _30_554 -> begin
(let _109_612 = (let _109_611 = (let _109_610 = (name_not_found lid)
in (_109_610, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_109_611))
in (Prims.raise _109_612))
end))

# 462 "FStar.Tc.Env.fst"
let lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ = (fun env lid -> (
# 463 "FStar.Tc.Env.fst"
let not_found = (fun _30_558 -> (match (()) with
| () -> begin
(let _109_621 = (let _109_620 = (let _109_619 = (name_not_found lid)
in (_109_619, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_109_620))
in (Prims.raise _109_621))
end))
in (
# 466 "FStar.Tc.Env.fst"
let mapper = (fun _30_6 -> (match (_30_6) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_30_561, t, (_30_564, tps, _30_567), _30_570, _30_572, _30_574)) -> begin
(let _109_626 = (let _109_625 = (FStar_List.map (fun _30_581 -> (match (_30_581) with
| (x, _30_580) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit (true)))
end)) tps)
in (FStar_Absyn_Util.close_typ _109_625 t))
in Some (_109_626))
end
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (l, t, qs, _30_588)) -> begin
if (in_cur_mod env l) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || env.is_iface) then begin
Some (t)
end else begin
None
end
end else begin
Some (t)
end
end
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_let ((_30_593, {FStar_Absyn_Syntax.lbname = _30_600; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _30_597; FStar_Absyn_Syntax.lbdef = _30_595}::[]), _30_605, _30_607, _30_609)) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_let ((_30_614, lbs), _30_618, _30_620, _30_622)) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (_30_628) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (lid') -> begin
if (FStar_Ident.lid_equals lid lid') then begin
Some (lb.FStar_Absyn_Syntax.lbtyp)
end else begin
None
end
end)))
end
| t -> begin
None
end))
in (match ((let _109_628 = (lookup_qname env lid)
in (FStar_Util.bind_opt _109_628 mapper))) with
| Some (t) -> begin
(
# 489 "FStar.Tc.Env.fst"
let _30_636 = t
in (let _109_629 = (FStar_Absyn_Syntax.range_of_lid lid)
in {FStar_Absyn_Syntax.n = _30_636.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _30_636.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = _109_629; FStar_Absyn_Syntax.fvs = _30_636.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _30_636.FStar_Absyn_Syntax.uvs}))
end
| None -> begin
(not_found ())
end))))

# 493 "FStar.Tc.Env.fst"
let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_30_642, _30_644, quals, _30_647))) -> begin
(FStar_All.pipe_right quals (FStar_Util.for_some (fun _30_7 -> (match (_30_7) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _30_655 -> begin
false
end))))
end
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_30_657, t, _30_660, _30_662, _30_664, _30_666))) -> begin
true
end
| _30_672 -> begin
false
end))

# 499 "FStar.Tc.Env.fst"
let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_30_676, _30_678, _30_680, _30_682, _30_684, tags, _30_687))) -> begin
(FStar_Util.for_some (fun _30_8 -> (match (_30_8) with
| (FStar_Absyn_Syntax.RecordType (_)) | (FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _30_700 -> begin
false
end)) tags)
end
| _30_702 -> begin
false
end))

# 505 "FStar.Tc.Env.fst"
let lookup_datacons_of_typ : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.typ) Prims.list Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_30_706, _30_708, _30_710, _30_712, datas, _30_715, _30_717))) -> begin
(let _109_646 = (FStar_List.map (fun l -> (let _109_645 = (lookup_lid env l)
in (l, _109_645))) datas)
in Some (_109_646))
end
| _30_724 -> begin
None
end))

# 510 "FStar.Tc.Env.fst"
let lookup_effect_abbrev : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.comp) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, binders, c, quals, _30_732))) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _30_9 -> (match (_30_9) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _30_740 -> begin
false
end)))) then begin
None
end else begin
Some ((binders, c))
end
end
| _30_742 -> begin
None
end))

# 518 "FStar.Tc.Env.fst"
let lookup_typ_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _30_748, t, quals, _30_752))) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _30_10 -> (match (_30_10) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _30_760 -> begin
false
end)))) then begin
None
end else begin
(
# 523 "FStar.Tc.Env.fst"
let t = (FStar_Absyn_Util.close_with_lam tps t)
in (let _109_657 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named ((t, lid))))
in Some (_109_657)))
end
end
| _30_763 -> begin
None
end))

# 527 "FStar.Tc.Env.fst"
let lookup_opaque_typ_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _30_769, t, quals, _30_773))) -> begin
(
# 530 "FStar.Tc.Env.fst"
let t = (FStar_Absyn_Util.close_with_lam tps t)
in (let _109_662 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named ((t, lid))))
in Some (_109_662)))
end
| _30_780 -> begin
None
end))

# 534 "FStar.Tc.Env.fst"
let lookup_btvdef : env  ->  FStar_Absyn_Syntax.btvdef  ->  FStar_Absyn_Syntax.knd Prims.option = (fun env btvd -> (FStar_Util.find_map env.gamma (fun _30_11 -> (match (_30_11) with
| Binding_typ (id, k) when (FStar_Absyn_Util.bvd_eq id btvd) -> begin
Some (k)
end
| _30_789 -> begin
None
end))))

# 539 "FStar.Tc.Env.fst"
let lookup_btvar : env  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Absyn_Syntax.knd = (fun env btv -> (match ((lookup_btvdef env btv.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _109_674 = (let _109_673 = (let _109_672 = (variable_not_found btv.FStar_Absyn_Syntax.v)
in (_109_672, (FStar_Absyn_Util.range_of_bvd btv.FStar_Absyn_Syntax.v)))
in FStar_Absyn_Syntax.Error (_109_673))
in (Prims.raise _109_674))
end
| Some (k) -> begin
k
end))

# 544 "FStar.Tc.Env.fst"
let lookup_typ_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd = (fun env ftv -> (match ((lookup_qname env ftv)) with
| (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _, _, _, _)))) | (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, _, _, _)))) -> begin
(FStar_Absyn_Util.close_kind tps k)
end
| _30_823 -> begin
(let _109_681 = (let _109_680 = (let _109_679 = (name_not_found ftv)
in (_109_679, (FStar_Ident.range_of_lid ftv)))
in FStar_Absyn_Syntax.Error (_109_680))
in (Prims.raise _109_681))
end))

# 552 "FStar.Tc.Env.fst"
let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_, _, _, _, _, quals, _)))) | (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_, _, quals, _)))) -> begin
(FStar_Util.for_some (fun _30_12 -> (match (_30_12) with
| FStar_Absyn_Syntax.Projector (_30_855) -> begin
true
end
| _30_858 -> begin
false
end)) quals)
end
| _30_860 -> begin
false
end))

# 559 "FStar.Tc.Env.fst"
let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_new_effect (ne, _30_865))) -> begin
(let _109_692 = (FStar_Absyn_Util.close_kind ne.FStar_Absyn_Syntax.binders ne.FStar_Absyn_Syntax.signature)
in (FStar_All.pipe_right _109_692 (fun _109_691 -> Some (_109_691))))
end
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, binders, _30_873, _30_875, _30_877))) -> begin
(let _109_694 = (FStar_Absyn_Util.close_kind binders FStar_Absyn_Syntax.mk_Kind_effect)
in (FStar_All.pipe_right _109_694 (fun _109_693 -> Some (_109_693))))
end
| _30_883 -> begin
None
end))

# 568 "FStar.Tc.Env.fst"
let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _109_701 = (let _109_700 = (let _109_699 = (name_not_found ftv)
in (_109_699, (FStar_Ident.range_of_lid ftv)))
in FStar_Absyn_Syntax.Error (_109_700))
in (Prims.raise _109_701))
end
| Some (k) -> begin
k
end))

# 573 "FStar.Tc.Env.fst"
let lookup_operator : env  ->  FStar_Ident.ident  ->  FStar_Absyn_Syntax.typ = (fun env opname -> (
# 574 "FStar.Tc.Env.fst"
let primName = (FStar_Ident.lid_of_path (("Prims")::((Prims.strcat "_dummy_" opname.FStar_Ident.idText))::[]) FStar_Absyn_Syntax.dummyRange)
in (lookup_lid env primName)))

# 577 "FStar.Tc.Env.fst"
let push_sigelt : env  ->  FStar_Absyn_Syntax.sigelt  ->  env = (fun env s -> (build_lattice (
# 577 "FStar.Tc.Env.fst"
let _30_894 = env
in {solver = _30_894.solver; range = _30_894.range; curmodule = _30_894.curmodule; gamma = (Binding_sig (s))::env.gamma; modules = _30_894.modules; expected_typ = _30_894.expected_typ; level = _30_894.level; sigtab = _30_894.sigtab; is_pattern = _30_894.is_pattern; instantiate_targs = _30_894.instantiate_targs; instantiate_vargs = _30_894.instantiate_vargs; effects = _30_894.effects; generalize = _30_894.generalize; letrecs = _30_894.letrecs; top_level = _30_894.top_level; check_uvars = _30_894.check_uvars; use_eq = _30_894.use_eq; is_iface = _30_894.is_iface; admit = _30_894.admit; default_effects = _30_894.default_effects}) s))

# 578 "FStar.Tc.Env.fst"
let push_local_binding : env  ->  binding  ->  env = (fun env b -> (
# 578 "FStar.Tc.Env.fst"
let _30_898 = env
in {solver = _30_898.solver; range = _30_898.range; curmodule = _30_898.curmodule; gamma = (b)::env.gamma; modules = _30_898.modules; expected_typ = _30_898.expected_typ; level = _30_898.level; sigtab = _30_898.sigtab; is_pattern = _30_898.is_pattern; instantiate_targs = _30_898.instantiate_targs; instantiate_vargs = _30_898.instantiate_vargs; effects = _30_898.effects; generalize = _30_898.generalize; letrecs = _30_898.letrecs; top_level = _30_898.top_level; check_uvars = _30_898.check_uvars; use_eq = _30_898.use_eq; is_iface = _30_898.is_iface; admit = _30_898.admit; default_effects = _30_898.default_effects}))

# 580 "FStar.Tc.Env.fst"
let uvars_in_env : env  ->  FStar_Absyn_Syntax.uvars = (fun env -> (
# 581 "FStar.Tc.Env.fst"
let no_uvs = (let _109_718 = (FStar_Absyn_Syntax.new_uv_set ())
in (let _109_717 = (FStar_Absyn_Syntax.new_uvt_set ())
in (let _109_716 = (FStar_Absyn_Syntax.new_uvt_set ())
in {FStar_Absyn_Syntax.uvars_k = _109_718; FStar_Absyn_Syntax.uvars_t = _109_717; FStar_Absyn_Syntax.uvars_e = _109_716})))
in (
# 586 "FStar.Tc.Env.fst"
let ext = (fun out uvs -> (
# 587 "FStar.Tc.Env.fst"
let _30_905 = out
in (let _109_725 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_k uvs.FStar_Absyn_Syntax.uvars_k)
in (let _109_724 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_t uvs.FStar_Absyn_Syntax.uvars_t)
in (let _109_723 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_e uvs.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _109_725; FStar_Absyn_Syntax.uvars_t = _109_724; FStar_Absyn_Syntax.uvars_e = _109_723})))))
in (
# 590 "FStar.Tc.Env.fst"
let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_lid (_, t)::tl) | (Binding_var (_, t)::tl) -> begin
(let _109_731 = (let _109_730 = (FStar_Absyn_Util.uvars_in_typ t)
in (ext out _109_730))
in (aux _109_731 tl))
end
| Binding_typ (_30_925, k)::tl -> begin
(let _109_733 = (let _109_732 = (FStar_Absyn_Util.uvars_in_kind k)
in (ext out _109_732))
in (aux _109_733 tl))
end
| Binding_sig (_30_933)::_30_931 -> begin
out
end))
in (aux no_uvs env.gamma)))))

# 598 "FStar.Tc.Env.fst"
let push_module : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env m -> (
# 599 "FStar.Tc.Env.fst"
let _30_938 = (add_sigelts env m.FStar_Absyn_Syntax.exports)
in (
# 600 "FStar.Tc.Env.fst"
let _30_940 = env
in {solver = _30_940.solver; range = _30_940.range; curmodule = _30_940.curmodule; gamma = []; modules = (m)::env.modules; expected_typ = None; level = _30_940.level; sigtab = _30_940.sigtab; is_pattern = _30_940.is_pattern; instantiate_targs = _30_940.instantiate_targs; instantiate_vargs = _30_940.instantiate_vargs; effects = _30_940.effects; generalize = _30_940.generalize; letrecs = _30_940.letrecs; top_level = _30_940.top_level; check_uvars = _30_940.check_uvars; use_eq = _30_940.use_eq; is_iface = _30_940.is_iface; admit = _30_940.admit; default_effects = _30_940.default_effects})))

# 605 "FStar.Tc.Env.fst"
let set_expected_typ : env  ->  FStar_Absyn_Syntax.typ  ->  env = (fun env t -> (match (t) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const ({FStar_Absyn_Syntax.v = _30_965; FStar_Absyn_Syntax.sort = {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _30_961; FStar_Absyn_Syntax.pos = _30_959; FStar_Absyn_Syntax.fvs = _30_957; FStar_Absyn_Syntax.uvs = _30_955}; FStar_Absyn_Syntax.p = _30_953}); FStar_Absyn_Syntax.tk = _30_951; FStar_Absyn_Syntax.pos = _30_949; FStar_Absyn_Syntax.fvs = _30_947; FStar_Absyn_Syntax.uvs = _30_945} -> begin
(let _109_743 = (let _109_742 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "Setting expected type to %s with kind unknown" _109_742))
in (FStar_All.failwith _109_743))
end
| _30_970 -> begin
(
# 608 "FStar.Tc.Env.fst"
let _30_971 = env
in {solver = _30_971.solver; range = _30_971.range; curmodule = _30_971.curmodule; gamma = _30_971.gamma; modules = _30_971.modules; expected_typ = Some (t); level = _30_971.level; sigtab = _30_971.sigtab; is_pattern = _30_971.is_pattern; instantiate_targs = _30_971.instantiate_targs; instantiate_vargs = _30_971.instantiate_vargs; effects = _30_971.effects; generalize = _30_971.generalize; letrecs = _30_971.letrecs; top_level = _30_971.top_level; check_uvars = _30_971.check_uvars; use_eq = false; is_iface = _30_971.is_iface; admit = _30_971.admit; default_effects = _30_971.default_effects})
end))

# 610 "FStar.Tc.Env.fst"
let expected_typ : env  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

# 613 "FStar.Tc.Env.fst"
let clear_expected_typ : env  ->  (env * FStar_Absyn_Syntax.typ Prims.option) = (fun env -> (let _109_748 = (expected_typ env)
in ((
# 613 "FStar.Tc.Env.fst"
let _30_978 = env
in {solver = _30_978.solver; range = _30_978.range; curmodule = _30_978.curmodule; gamma = _30_978.gamma; modules = _30_978.modules; expected_typ = None; level = _30_978.level; sigtab = _30_978.sigtab; is_pattern = _30_978.is_pattern; instantiate_targs = _30_978.instantiate_targs; instantiate_vargs = _30_978.instantiate_vargs; effects = _30_978.effects; generalize = _30_978.generalize; letrecs = _30_978.letrecs; top_level = _30_978.top_level; check_uvars = _30_978.check_uvars; use_eq = false; is_iface = _30_978.is_iface; admit = _30_978.admit; default_effects = _30_978.default_effects}), _109_748)))

# 615 "FStar.Tc.Env.fst"
let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))

# 617 "FStar.Tc.Env.fst"
let binding_of_binder : FStar_Absyn_Syntax.binder  ->  binding = (fun b -> (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
Binding_typ ((a.FStar_Absyn_Syntax.v, a.FStar_Absyn_Syntax.sort))
end
| FStar_Util.Inr (x) -> begin
Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))
end))

# 621 "FStar.Tc.Env.fst"
let binders : env  ->  FStar_Absyn_Syntax.binders = (fun env -> (FStar_List.fold_left (fun out b -> (match (b) with
| Binding_var (x, t) -> begin
(let _109_766 = (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_109_766)::out)
end
| Binding_typ (a, k) -> begin
(let _109_767 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_109_767)::out)
end
| _30_1002 -> begin
out
end)) [] env.gamma))

# 627 "FStar.Tc.Env.fst"
let t_binders : env  ->  FStar_Absyn_Syntax.binders = (fun env -> (FStar_List.fold_left (fun out b -> (match (b) with
| Binding_var (_30_1007) -> begin
out
end
| Binding_typ (a, k) -> begin
(let _109_772 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_109_772)::out)
end
| _30_1014 -> begin
out
end)) [] env.gamma))

# 633 "FStar.Tc.Env.fst"
let idents : env  ->  FStar_Absyn_Syntax.freevars = (fun env -> (let _109_776 = (let _109_775 = (binders env)
in (FStar_All.pipe_right _109_775 (FStar_List.map Prims.fst)))
in (FStar_Absyn_Syntax.freevars_of_list _109_776)))

# 635 "FStar.Tc.Env.fst"
let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (
# 636 "FStar.Tc.Env.fst"
let keys = (FStar_List.fold_left (fun keys _30_13 -> (match (_30_13) with
| Binding_sig (s) -> begin
(let _109_781 = (FStar_Absyn_Util.lids_of_sigelt s)
in (FStar_List.append _109_781 keys))
end
| _30_1022 -> begin
keys
end)) [] env.gamma)
in (let _109_786 = (sigtab env)
in (FStar_Util.smap_fold _109_786 (fun _30_1024 v keys -> (let _109_785 = (FStar_Absyn_Util.lids_of_sigelt v)
in (FStar_List.append _109_785 keys))) keys))))




