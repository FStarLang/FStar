
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
let ___Binding_var____0 : binding  ->  (FStar_Absyn_Syntax.bvvdef * FStar_Absyn_Syntax.typ) = (fun projectee -> (match (projectee) with
| Binding_var (_37_16) -> begin
_37_16
end))

# 30 "FStar.Tc.Env.fst"
let ___Binding_typ____0 : binding  ->  (FStar_Absyn_Syntax.btvdef * FStar_Absyn_Syntax.knd) = (fun projectee -> (match (projectee) with
| Binding_typ (_37_19) -> begin
_37_19
end))

# 31 "FStar.Tc.Env.fst"
let ___Binding_lid____0 : binding  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.typ) = (fun projectee -> (match (projectee) with
| Binding_lid (_37_22) -> begin
_37_22
end))

# 32 "FStar.Tc.Env.fst"
let ___Binding_sig____0 : binding  ->  FStar_Absyn_Syntax.sigelt = (fun projectee -> (match (projectee) with
| Binding_sig (_37_25) -> begin
_37_25
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
let _37_35 = (FStar_List.iter (fun se -> (
# 42 "FStar.Tc.Env.fst"
let lids = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (FStar_Util.smap_add ht l.FStar_Ident.str se)) lids))) s)
in ht)))

# 46 "FStar.Tc.Env.fst"
let modules_to_sigtables = (fun mods -> (let _116_65 = (FStar_List.collect (fun _37_41 -> (match (_37_41) with
| (_37_39, m) -> begin
m.FStar_Absyn_Syntax.declarations
end)) mods)
in (signature_to_sigtables _116_65)))

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
let bound_vars : env  ->  (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either Prims.list = (fun env -> (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _37_1 -> (match (_37_1) with
| Binding_typ (a, k) -> begin
(let _116_291 = (FStar_All.pipe_left (fun _116_290 -> FStar_Util.Inl (_116_290)) (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_116_291)::[])
end
| Binding_var (x, t) -> begin
(let _116_293 = (FStar_All.pipe_left (fun _116_292 -> FStar_Util.Inr (_116_292)) (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_116_293)::[])
end
| Binding_lid (_37_96) -> begin
[]
end
| Binding_sig (_37_99) -> begin
[]
end)))))

# 167 "FStar.Tc.Env.fst"
let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Absyn_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Absyn_Syntax.name l))))))

# 170 "FStar.Tc.Env.fst"
let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> ((let _116_304 = (FStar_ST.read FStar_Options.debug)
in (FStar_All.pipe_right _116_304 (FStar_Util.for_some (fun x -> (env.curmodule.FStar_Ident.str = x))))) && (FStar_Options.debug_level_geq l)))

# 173 "FStar.Tc.Env.fst"
let show : env  ->  Prims.bool = (fun env -> (let _116_308 = (FStar_ST.read FStar_Options.show_signatures)
in (FStar_All.pipe_right _116_308 (FStar_Util.for_some (fun x -> (env.curmodule.FStar_Ident.str = x))))))

# 175 "FStar.Tc.Env.fst"
let new_sigtab = (fun _37_109 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))

# 176 "FStar.Tc.Env.fst"
let sigtab : env  ->  sigtable = (fun env -> (FStar_List.hd env.sigtab))

# 177 "FStar.Tc.Env.fst"
let push : env  ->  Prims.string  ->  env = (fun env msg -> (
# 178 "FStar.Tc.Env.fst"
let _37_113 = (env.solver.push msg)
in (
# 179 "FStar.Tc.Env.fst"
let _37_115 = env
in (let _116_318 = (let _116_317 = (let _116_316 = (sigtab env)
in (FStar_Util.smap_copy _116_316))
in (_116_317)::env.sigtab)
in {solver = _37_115.solver; range = _37_115.range; curmodule = _37_115.curmodule; gamma = _37_115.gamma; modules = _37_115.modules; expected_typ = _37_115.expected_typ; level = _37_115.level; sigtab = _116_318; is_pattern = _37_115.is_pattern; instantiate_targs = _37_115.instantiate_targs; instantiate_vargs = _37_115.instantiate_vargs; effects = _37_115.effects; generalize = _37_115.generalize; letrecs = _37_115.letrecs; top_level = _37_115.top_level; check_uvars = _37_115.check_uvars; use_eq = _37_115.use_eq; is_iface = _37_115.is_iface; admit = _37_115.admit; default_effects = _37_115.default_effects}))))

# 180 "FStar.Tc.Env.fst"
let mark : env  ->  env = (fun env -> (
# 181 "FStar.Tc.Env.fst"
let _37_118 = (env.solver.mark "USER MARK")
in (
# 182 "FStar.Tc.Env.fst"
let _37_120 = env
in (let _116_323 = (let _116_322 = (let _116_321 = (sigtab env)
in (FStar_Util.smap_copy _116_321))
in (_116_322)::env.sigtab)
in {solver = _37_120.solver; range = _37_120.range; curmodule = _37_120.curmodule; gamma = _37_120.gamma; modules = _37_120.modules; expected_typ = _37_120.expected_typ; level = _37_120.level; sigtab = _116_323; is_pattern = _37_120.is_pattern; instantiate_targs = _37_120.instantiate_targs; instantiate_vargs = _37_120.instantiate_vargs; effects = _37_120.effects; generalize = _37_120.generalize; letrecs = _37_120.letrecs; top_level = _37_120.top_level; check_uvars = _37_120.check_uvars; use_eq = _37_120.use_eq; is_iface = _37_120.is_iface; admit = _37_120.admit; default_effects = _37_120.default_effects}))))

# 183 "FStar.Tc.Env.fst"
let commit_mark : env  ->  env = (fun env -> (
# 184 "FStar.Tc.Env.fst"
let _37_123 = (env.solver.commit_mark "USER MARK")
in (
# 185 "FStar.Tc.Env.fst"
let sigtab = (match (env.sigtab) with
| hd::_37_127::tl -> begin
(hd)::tl
end
| _37_132 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 188 "FStar.Tc.Env.fst"
let _37_134 = env
in {solver = _37_134.solver; range = _37_134.range; curmodule = _37_134.curmodule; gamma = _37_134.gamma; modules = _37_134.modules; expected_typ = _37_134.expected_typ; level = _37_134.level; sigtab = sigtab; is_pattern = _37_134.is_pattern; instantiate_targs = _37_134.instantiate_targs; instantiate_vargs = _37_134.instantiate_vargs; effects = _37_134.effects; generalize = _37_134.generalize; letrecs = _37_134.letrecs; top_level = _37_134.top_level; check_uvars = _37_134.check_uvars; use_eq = _37_134.use_eq; is_iface = _37_134.is_iface; admit = _37_134.admit; default_effects = _37_134.default_effects}))))

# 189 "FStar.Tc.Env.fst"
let reset_mark : env  ->  env = (fun env -> (
# 190 "FStar.Tc.Env.fst"
let _37_137 = (env.solver.reset_mark "USER MARK")
in (
# 191 "FStar.Tc.Env.fst"
let _37_139 = env
in (let _116_328 = (FStar_List.tl env.sigtab)
in {solver = _37_139.solver; range = _37_139.range; curmodule = _37_139.curmodule; gamma = _37_139.gamma; modules = _37_139.modules; expected_typ = _37_139.expected_typ; level = _37_139.level; sigtab = _116_328; is_pattern = _37_139.is_pattern; instantiate_targs = _37_139.instantiate_targs; instantiate_vargs = _37_139.instantiate_vargs; effects = _37_139.effects; generalize = _37_139.generalize; letrecs = _37_139.letrecs; top_level = _37_139.top_level; check_uvars = _37_139.check_uvars; use_eq = _37_139.use_eq; is_iface = _37_139.is_iface; admit = _37_139.admit; default_effects = _37_139.default_effects}))))

# 192 "FStar.Tc.Env.fst"
let pop : env  ->  Prims.string  ->  env = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(FStar_All.failwith "Too many pops")
end
| _37_149::tl -> begin
(
# 196 "FStar.Tc.Env.fst"
let _37_151 = (env.solver.pop msg)
in (
# 197 "FStar.Tc.Env.fst"
let _37_153 = env
in {solver = _37_153.solver; range = _37_153.range; curmodule = _37_153.curmodule; gamma = _37_153.gamma; modules = _37_153.modules; expected_typ = _37_153.expected_typ; level = _37_153.level; sigtab = tl; is_pattern = _37_153.is_pattern; instantiate_targs = _37_153.instantiate_targs; instantiate_vargs = _37_153.instantiate_vargs; effects = _37_153.effects; generalize = _37_153.generalize; letrecs = _37_153.letrecs; top_level = _37_153.top_level; check_uvars = _37_153.check_uvars; use_eq = _37_153.use_eq; is_iface = _37_153.is_iface; admit = _37_153.admit; default_effects = _37_153.default_effects}))
end))

# 199 "FStar.Tc.Env.fst"
let initial_env : solver_t  ->  FStar_Ident.lident  ->  env = (fun solver module_lid -> (let _116_338 = (let _116_337 = (new_sigtab ())
in (_116_337)::[])
in {solver = solver; range = FStar_Absyn_Syntax.dummyRange; curmodule = module_lid; gamma = []; modules = []; expected_typ = None; level = Expr; sigtab = _116_338; is_pattern = false; instantiate_targs = true; instantiate_vargs = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = true; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []}))

# 223 "FStar.Tc.Env.fst"
let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Absyn_Syntax.mname l)))))

# 226 "FStar.Tc.Env.fst"
let name_not_found : FStar_Absyn_Syntax.lident  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))

# 229 "FStar.Tc.Env.fst"
let variable_not_found = (fun v -> (let _116_347 = (FStar_Absyn_Print.strBvd v)
in (FStar_Util.format1 "Variable \"%s\" not found" _116_347)))

# 232 "FStar.Tc.Env.fst"
let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _116_354 = (let _116_353 = (let _116_352 = (name_not_found l)
in (_116_352, (FStar_Ident.range_of_lid l)))
in FStar_Absyn_Syntax.Error (_116_353))
in (Prims.raise _116_354))
end
| Some (md) -> begin
md
end))

# 237 "FStar.Tc.Env.fst"
let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
(l1, (fun t wp -> wp), (fun t wp -> wp))
end else begin
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _37_182 -> (match (_37_182) with
| (m1, m2, _37_177, _37_179, _37_181) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _116_410 = (let _116_409 = (let _116_408 = (let _116_407 = (FStar_Absyn_Print.sli l1)
in (let _116_406 = (FStar_Absyn_Print.sli l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _116_407 _116_406)))
in (_116_408, env.range))
in FStar_Absyn_Syntax.Error (_116_409))
in (Prims.raise _116_410))
end
| Some (_37_185, _37_187, m3, j1, j2) -> begin
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
(let _116_425 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _116_425))
end
| Some (md) -> begin
(match (md.FStar_Absyn_Syntax.signature.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow ((FStar_Util.Inl (a), _37_218)::(FStar_Util.Inl (wp), _37_213)::(FStar_Util.Inl (wlp), _37_208)::[], {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_effect; FStar_Absyn_Syntax.tk = _37_228; FStar_Absyn_Syntax.pos = _37_226; FStar_Absyn_Syntax.fvs = _37_224; FStar_Absyn_Syntax.uvs = _37_222}) -> begin
(a, wp.FStar_Absyn_Syntax.sort)
end
| _37_234 -> begin
(FStar_All.failwith "Impossible")
end)
end))

# 257 "FStar.Tc.Env.fst"
let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.btvar * FStar_Absyn_Syntax.knd) = (fun env m -> (wp_sig_aux env.effects.decls m))

# 259 "FStar.Tc.Env.fst"
let default_effect : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (FStar_Util.find_map env.default_effects (fun _37_241 -> (match (_37_241) with
| (l', m) -> begin
if (FStar_Ident.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))

# 261 "FStar.Tc.Env.fst"
let build_lattice : env  ->  FStar_Absyn_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Absyn_Syntax.Sig_effect_abbrev (l, _37_246, c, quals, r) -> begin
(match ((FStar_Util.find_map quals (fun _37_2 -> (match (_37_2) with
| FStar_Absyn_Syntax.DefaultEffect (n) -> begin
n
end
| _37_256 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(
# 265 "FStar.Tc.Env.fst"
let _37_260 = env
in {solver = _37_260.solver; range = _37_260.range; curmodule = _37_260.curmodule; gamma = _37_260.gamma; modules = _37_260.modules; expected_typ = _37_260.expected_typ; level = _37_260.level; sigtab = _37_260.sigtab; is_pattern = _37_260.is_pattern; instantiate_targs = _37_260.instantiate_targs; instantiate_vargs = _37_260.instantiate_vargs; effects = _37_260.effects; generalize = _37_260.generalize; letrecs = _37_260.letrecs; top_level = _37_260.top_level; check_uvars = _37_260.check_uvars; use_eq = _37_260.use_eq; is_iface = _37_260.is_iface; admit = _37_260.admit; default_effects = ((e, l))::env.default_effects})
end)
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, _37_264) -> begin
(
# 268 "FStar.Tc.Env.fst"
let effects = (
# 268 "FStar.Tc.Env.fst"
let _37_267 = env.effects
in {decls = (ne)::env.effects.decls; order = _37_267.order; joins = _37_267.joins})
in (
# 269 "FStar.Tc.Env.fst"
let _37_270 = env
in {solver = _37_270.solver; range = _37_270.range; curmodule = _37_270.curmodule; gamma = _37_270.gamma; modules = _37_270.modules; expected_typ = _37_270.expected_typ; level = _37_270.level; sigtab = _37_270.sigtab; is_pattern = _37_270.is_pattern; instantiate_targs = _37_270.instantiate_targs; instantiate_vargs = _37_270.instantiate_vargs; effects = effects; generalize = _37_270.generalize; letrecs = _37_270.letrecs; top_level = _37_270.top_level; check_uvars = _37_270.check_uvars; use_eq = _37_270.use_eq; is_iface = _37_270.is_iface; admit = _37_270.admit; default_effects = _37_270.default_effects}))
end
| FStar_Absyn_Syntax.Sig_sub_effect (sub, _37_274) -> begin
(
# 272 "FStar.Tc.Env.fst"
let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _116_446 = (e1.mlift r wp1)
in (e2.mlift r _116_446)))})
in (
# 277 "FStar.Tc.Env.fst"
let mk_lift = (fun lift_t r wp1 -> (let _116_457 = (let _116_456 = (let _116_455 = (FStar_Absyn_Syntax.targ r)
in (let _116_454 = (let _116_453 = (FStar_Absyn_Syntax.targ wp1)
in (_116_453)::[])
in (_116_455)::_116_454))
in (lift_t, _116_456))
in (FStar_Absyn_Syntax.mk_Typ_app _116_457 None wp1.FStar_Absyn_Syntax.pos)))
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
let arg = (let _116_474 = (FStar_Absyn_Syntax.lid_of_path (("ARG")::[]) FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Util.ftv _116_474 FStar_Absyn_Syntax.mk_Kind_type))
in (
# 290 "FStar.Tc.Env.fst"
let wp = (let _116_475 = (FStar_Absyn_Syntax.lid_of_path (("WP")::[]) FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Util.ftv _116_475 FStar_Absyn_Syntax.mk_Kind_unknown))
in (let _116_476 = (l arg wp)
in (FStar_Absyn_Print.typ_to_string _116_476)))))
in (
# 292 "FStar.Tc.Env.fst"
let order = (edge)::env.effects.order
in (
# 294 "FStar.Tc.Env.fst"
let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Absyn_Syntax.mname)))
in (
# 296 "FStar.Tc.Env.fst"
let find_edge = (fun order _37_302 -> (match (_37_302) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _116_482 -> Some (_116_482)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (
# 305 "FStar.Tc.Env.fst"
let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _116_490 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _116_489 = (find_edge order (i, k))
in (let _116_488 = (find_edge order (k, j))
in (_116_489, _116_488)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _37_314 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _116_490))) order))
in (
# 316 "FStar.Tc.Env.fst"
let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (
# 318 "FStar.Tc.Env.fst"
let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (
# 321 "FStar.Tc.Env.fst"
let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _116_498 = (find_edge order (i, k))
in (let _116_497 = (find_edge order (j, k))
in (_116_498, _116_497)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _37_331, _37_333) -> begin
if ((let _116_499 = (find_edge order (k, ub))
in (FStar_Util.is_some _116_499)) && (not ((let _116_500 = (find_edge order (ub, k))
in (FStar_Util.is_some _116_500))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _37_337 -> begin
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
let _37_346 = env.effects
in {decls = _37_346.decls; order = order; joins = joins})
in (
# 341 "FStar.Tc.Env.fst"
let _37_349 = env
in {solver = _37_349.solver; range = _37_349.range; curmodule = _37_349.curmodule; gamma = _37_349.gamma; modules = _37_349.modules; expected_typ = _37_349.expected_typ; level = _37_349.level; sigtab = _37_349.sigtab; is_pattern = _37_349.is_pattern; instantiate_targs = _37_349.instantiate_targs; instantiate_vargs = _37_349.instantiate_vargs; effects = effects; generalize = _37_349.generalize; letrecs = _37_349.letrecs; top_level = _37_349.top_level; check_uvars = _37_349.check_uvars; use_eq = _37_349.use_eq; is_iface = _37_349.is_iface; admit = _37_349.admit; default_effects = _37_349.default_effects})))))))))))))
end
| _37_352 -> begin
env
end))

# 346 "FStar.Tc.Env.fst"
let rec add_sigelt : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Absyn_Syntax.Sig_bundle (ses, _37_357, _37_359, _37_361) -> begin
(add_sigelts env ses)
end
| _37_365 -> begin
(
# 349 "FStar.Tc.Env.fst"
let lids = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _116_508 = (sigtab env)
in (FStar_Util.smap_add _116_508 l.FStar_Ident.str se))) lids))
end))
and add_sigelts : env  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))

# 355 "FStar.Tc.Env.fst"
let empty_lid : FStar_Absyn_Syntax.lident = (let _116_512 = (let _116_511 = (FStar_Absyn_Syntax.id_of_text "")
in (_116_511)::[])
in (FStar_Absyn_Syntax.lid_of_ids _116_512))

# 357 "FStar.Tc.Env.fst"
let finish_module : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env m -> (
# 358 "FStar.Tc.Env.fst"
let sigs = if (FStar_Ident.lid_equals m.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid) then begin
(FStar_All.pipe_right env.gamma (FStar_List.collect (fun _37_3 -> (match (_37_3) with
| Binding_sig (se) -> begin
(se)::[]
end
| _37_376 -> begin
[]
end))))
end else begin
m.FStar_Absyn_Syntax.exports
end
in (
# 364 "FStar.Tc.Env.fst"
let _37_378 = (add_sigelts env sigs)
in (
# 365 "FStar.Tc.Env.fst"
let _37_380 = env
in {solver = _37_380.solver; range = _37_380.range; curmodule = empty_lid; gamma = []; modules = (m)::env.modules; expected_typ = _37_380.expected_typ; level = _37_380.level; sigtab = _37_380.sigtab; is_pattern = _37_380.is_pattern; instantiate_targs = _37_380.instantiate_targs; instantiate_vargs = _37_380.instantiate_vargs; effects = _37_380.effects; generalize = _37_380.generalize; letrecs = _37_380.letrecs; top_level = _37_380.top_level; check_uvars = _37_380.check_uvars; use_eq = _37_380.use_eq; is_iface = _37_380.is_iface; admit = _37_380.admit; default_effects = _37_380.default_effects}))))

# 371 "FStar.Tc.Env.fst"
let set_level : env  ->  level  ->  env = (fun env level -> (
# 371 "FStar.Tc.Env.fst"
let _37_384 = env
in {solver = _37_384.solver; range = _37_384.range; curmodule = _37_384.curmodule; gamma = _37_384.gamma; modules = _37_384.modules; expected_typ = _37_384.expected_typ; level = level; sigtab = _37_384.sigtab; is_pattern = _37_384.is_pattern; instantiate_targs = _37_384.instantiate_targs; instantiate_vargs = _37_384.instantiate_vargs; effects = _37_384.effects; generalize = _37_384.generalize; letrecs = _37_384.letrecs; top_level = _37_384.top_level; check_uvars = _37_384.check_uvars; use_eq = _37_384.use_eq; is_iface = _37_384.is_iface; admit = _37_384.admit; default_effects = _37_384.default_effects}))

# 372 "FStar.Tc.Env.fst"
let is_level : env  ->  level  ->  Prims.bool = (fun env level -> (env.level = level))

# 373 "FStar.Tc.Env.fst"
let modules : env  ->  FStar_Absyn_Syntax.modul Prims.list = (fun env -> env.modules)

# 374 "FStar.Tc.Env.fst"
let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)

# 375 "FStar.Tc.Env.fst"
let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (
# 375 "FStar.Tc.Env.fst"
let _37_392 = env
in {solver = _37_392.solver; range = _37_392.range; curmodule = lid; gamma = _37_392.gamma; modules = _37_392.modules; expected_typ = _37_392.expected_typ; level = _37_392.level; sigtab = _37_392.sigtab; is_pattern = _37_392.is_pattern; instantiate_targs = _37_392.instantiate_targs; instantiate_vargs = _37_392.instantiate_vargs; effects = _37_392.effects; generalize = _37_392.generalize; letrecs = _37_392.letrecs; top_level = _37_392.top_level; check_uvars = _37_392.check_uvars; use_eq = _37_392.use_eq; is_iface = _37_392.is_iface; admit = _37_392.admit; default_effects = _37_392.default_effects}))

# 376 "FStar.Tc.Env.fst"
let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Absyn_Syntax.dummyRange) then begin
e
end else begin
(
# 376 "FStar.Tc.Env.fst"
let _37_396 = e
in {solver = _37_396.solver; range = r; curmodule = _37_396.curmodule; gamma = _37_396.gamma; modules = _37_396.modules; expected_typ = _37_396.expected_typ; level = _37_396.level; sigtab = _37_396.sigtab; is_pattern = _37_396.is_pattern; instantiate_targs = _37_396.instantiate_targs; instantiate_vargs = _37_396.instantiate_vargs; effects = _37_396.effects; generalize = _37_396.generalize; letrecs = _37_396.letrecs; top_level = _37_396.top_level; check_uvars = _37_396.check_uvars; use_eq = _37_396.use_eq; is_iface = _37_396.is_iface; admit = _37_396.admit; default_effects = _37_396.default_effects})
end)

# 377 "FStar.Tc.Env.fst"
let get_range : env  ->  FStar_Range.range = (fun e -> e.range)

# 378 "FStar.Tc.Env.fst"
let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.sigelt Prims.option = (fun env lid -> (let _116_544 = (sigtab env)
in (FStar_Util.smap_try_find _116_544 (FStar_Ident.text_of_lid lid))))

# 380 "FStar.Tc.Env.fst"
let lookup_bvvdef : env  ->  FStar_Absyn_Syntax.bvvdef  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env bvvd -> (FStar_Util.find_map env.gamma (fun _37_4 -> (match (_37_4) with
| Binding_var (id, t) when (FStar_Absyn_Util.bvd_eq id bvvd) -> begin
Some (t)
end
| _37_409 -> begin
None
end))))

# 385 "FStar.Tc.Env.fst"
let lookup_bvar : env  ->  FStar_Absyn_Syntax.bvvar  ->  FStar_Absyn_Syntax.typ = (fun env bv -> (match ((lookup_bvvdef env bv.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _116_556 = (let _116_555 = (let _116_554 = (variable_not_found bv.FStar_Absyn_Syntax.v)
in (_116_554, (FStar_Absyn_Util.range_of_bvd bv.FStar_Absyn_Syntax.v)))
in FStar_Absyn_Syntax.Error (_116_555))
in (Prims.raise _116_556))
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
| ([], _37_425) -> begin
true
end
| (_37_428, []) -> begin
false
end
| (hd::tl, hd'::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _37_439 -> begin
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
(FStar_Util.find_map env.gamma (fun _37_5 -> (match (_37_5) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
Some (FStar_Util.Inl (t))
end else begin
None
end
end
| Binding_sig (FStar_Absyn_Syntax.Sig_bundle (ses, _37_450, _37_452, _37_454)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _116_571 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _116_571 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
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
| _37_463 -> begin
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
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_37_471, t, (_37_474, tps, _37_477), _37_480, _37_482, _37_484))) -> begin
(let _116_577 = (FStar_List.map (fun _37_492 -> (match (_37_492) with
| (x, _37_491) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit (true)))
end)) tps)
in (FStar_Absyn_Util.close_typ _116_577 t))
end
| _37_494 -> begin
(let _116_580 = (let _116_579 = (let _116_578 = (name_not_found lid)
in (_116_578, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_116_579))
in (Prims.raise _116_580))
end))

# 433 "FStar.Tc.Env.fst"
let lookup_kind_abbrev : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_kind_abbrev (l, binders, k, _37_501))) -> begin
(l, binders, k)
end
| _37_507 -> begin
(let _116_587 = (let _116_586 = (let _116_585 = (name_not_found lid)
in (_116_585, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_116_586))
in (Prims.raise _116_587))
end))

# 438 "FStar.Tc.Env.fst"
let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (
# 439 "FStar.Tc.Env.fst"
let fail = (fun _37_512 -> (match (()) with
| () -> begin
(let _116_598 = (let _116_597 = (FStar_Util.string_of_int i)
in (let _116_596 = (FStar_Absyn_Print.sli lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _116_597 _116_596)))
in (FStar_All.failwith _116_598))
end))
in (
# 440 "FStar.Tc.Env.fst"
let t = (lookup_datacon env lid)
in (match ((let _116_599 = (FStar_Absyn_Util.compress_typ t)
in _116_599.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, _37_516) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(
# 445 "FStar.Tc.Env.fst"
let b = (FStar_List.nth binders i)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _116_600 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (FStar_All.pipe_right _116_600 Prims.fst))
end
| FStar_Util.Inr (x) -> begin
(let _116_601 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (FStar_All.pipe_right _116_601 Prims.fst))
end))
end
end
| _37_525 -> begin
(fail ())
end))))

# 452 "FStar.Tc.Env.fst"
let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_37_529, t, q, _37_533))) -> begin
Some ((t, q))
end
| _37_539 -> begin
None
end))

# 457 "FStar.Tc.Env.fst"
let lookup_val_decl : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_37_543, t, _37_546, _37_548))) -> begin
t
end
| _37_554 -> begin
(let _116_612 = (let _116_611 = (let _116_610 = (name_not_found lid)
in (_116_610, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_116_611))
in (Prims.raise _116_612))
end))

# 462 "FStar.Tc.Env.fst"
let lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ = (fun env lid -> (
# 463 "FStar.Tc.Env.fst"
let not_found = (fun _37_558 -> (match (()) with
| () -> begin
(let _116_621 = (let _116_620 = (let _116_619 = (name_not_found lid)
in (_116_619, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_116_620))
in (Prims.raise _116_621))
end))
in (
# 466 "FStar.Tc.Env.fst"
let mapper = (fun _37_6 -> (match (_37_6) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_37_561, t, (_37_564, tps, _37_567), _37_570, _37_572, _37_574)) -> begin
(let _116_626 = (let _116_625 = (FStar_List.map (fun _37_581 -> (match (_37_581) with
| (x, _37_580) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit (true)))
end)) tps)
in (FStar_Absyn_Util.close_typ _116_625 t))
in Some (_116_626))
end
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (l, t, qs, _37_588)) -> begin
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
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_let ((_37_593, {FStar_Absyn_Syntax.lbname = _37_600; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _37_597; FStar_Absyn_Syntax.lbdef = _37_595}::[]), _37_605, _37_607, _37_609)) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_let ((_37_614, lbs), _37_618, _37_620, _37_622)) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (_37_628) -> begin
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
in (match ((let _116_628 = (lookup_qname env lid)
in (FStar_Util.bind_opt _116_628 mapper))) with
| Some (t) -> begin
(
# 489 "FStar.Tc.Env.fst"
let _37_636 = t
in (let _116_629 = (FStar_Absyn_Syntax.range_of_lid lid)
in {FStar_Absyn_Syntax.n = _37_636.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _37_636.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = _116_629; FStar_Absyn_Syntax.fvs = _37_636.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _37_636.FStar_Absyn_Syntax.uvs}))
end
| None -> begin
(not_found ())
end))))

# 493 "FStar.Tc.Env.fst"
let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_37_642, _37_644, quals, _37_647))) -> begin
(FStar_All.pipe_right quals (FStar_Util.for_some (fun _37_7 -> (match (_37_7) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _37_655 -> begin
false
end))))
end
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_37_657, t, _37_660, _37_662, _37_664, _37_666))) -> begin
true
end
| _37_672 -> begin
false
end))

# 499 "FStar.Tc.Env.fst"
let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_37_676, _37_678, _37_680, _37_682, _37_684, tags, _37_687))) -> begin
(FStar_Util.for_some (fun _37_8 -> (match (_37_8) with
| (FStar_Absyn_Syntax.RecordType (_)) | (FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _37_700 -> begin
false
end)) tags)
end
| _37_702 -> begin
false
end))

# 505 "FStar.Tc.Env.fst"
let lookup_datacons_of_typ : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.typ) Prims.list Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_37_706, _37_708, _37_710, _37_712, datas, _37_715, _37_717))) -> begin
(let _116_646 = (FStar_List.map (fun l -> (let _116_645 = (lookup_lid env l)
in (l, _116_645))) datas)
in Some (_116_646))
end
| _37_724 -> begin
None
end))

# 510 "FStar.Tc.Env.fst"
let lookup_effect_abbrev : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.comp) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, binders, c, quals, _37_732))) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _37_9 -> (match (_37_9) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _37_740 -> begin
false
end)))) then begin
None
end else begin
Some ((binders, c))
end
end
| _37_742 -> begin
None
end))

# 518 "FStar.Tc.Env.fst"
let lookup_typ_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _37_748, t, quals, _37_752))) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _37_10 -> (match (_37_10) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _37_760 -> begin
false
end)))) then begin
None
end else begin
(
# 523 "FStar.Tc.Env.fst"
let t = (FStar_Absyn_Util.close_with_lam tps t)
in (let _116_657 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named ((t, lid))))
in Some (_116_657)))
end
end
| _37_763 -> begin
None
end))

# 527 "FStar.Tc.Env.fst"
let lookup_opaque_typ_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _37_769, t, quals, _37_773))) -> begin
(
# 530 "FStar.Tc.Env.fst"
let t = (FStar_Absyn_Util.close_with_lam tps t)
in (let _116_662 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named ((t, lid))))
in Some (_116_662)))
end
| _37_780 -> begin
None
end))

# 534 "FStar.Tc.Env.fst"
let lookup_btvdef : env  ->  FStar_Absyn_Syntax.btvdef  ->  FStar_Absyn_Syntax.knd Prims.option = (fun env btvd -> (FStar_Util.find_map env.gamma (fun _37_11 -> (match (_37_11) with
| Binding_typ (id, k) when (FStar_Absyn_Util.bvd_eq id btvd) -> begin
Some (k)
end
| _37_789 -> begin
None
end))))

# 539 "FStar.Tc.Env.fst"
let lookup_btvar : env  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Absyn_Syntax.knd = (fun env btv -> (match ((lookup_btvdef env btv.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _116_674 = (let _116_673 = (let _116_672 = (variable_not_found btv.FStar_Absyn_Syntax.v)
in (_116_672, (FStar_Absyn_Util.range_of_bvd btv.FStar_Absyn_Syntax.v)))
in FStar_Absyn_Syntax.Error (_116_673))
in (Prims.raise _116_674))
end
| Some (k) -> begin
k
end))

# 544 "FStar.Tc.Env.fst"
let lookup_typ_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd = (fun env ftv -> (match ((lookup_qname env ftv)) with
| (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _, _, _, _)))) | (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, _, _, _)))) -> begin
(FStar_Absyn_Util.close_kind tps k)
end
| _37_823 -> begin
(let _116_681 = (let _116_680 = (let _116_679 = (name_not_found ftv)
in (_116_679, (FStar_Ident.range_of_lid ftv)))
in FStar_Absyn_Syntax.Error (_116_680))
in (Prims.raise _116_681))
end))

# 552 "FStar.Tc.Env.fst"
let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_, _, _, _, _, quals, _)))) | (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_, _, quals, _)))) -> begin
(FStar_Util.for_some (fun _37_12 -> (match (_37_12) with
| FStar_Absyn_Syntax.Projector (_37_855) -> begin
true
end
| _37_858 -> begin
false
end)) quals)
end
| _37_860 -> begin
false
end))

# 559 "FStar.Tc.Env.fst"
let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_new_effect (ne, _37_865))) -> begin
(let _116_692 = (FStar_Absyn_Util.close_kind ne.FStar_Absyn_Syntax.binders ne.FStar_Absyn_Syntax.signature)
in (FStar_All.pipe_right _116_692 (fun _116_691 -> Some (_116_691))))
end
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, binders, _37_873, _37_875, _37_877))) -> begin
(let _116_694 = (FStar_Absyn_Util.close_kind binders FStar_Absyn_Syntax.mk_Kind_effect)
in (FStar_All.pipe_right _116_694 (fun _116_693 -> Some (_116_693))))
end
| _37_883 -> begin
None
end))

# 568 "FStar.Tc.Env.fst"
let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _116_701 = (let _116_700 = (let _116_699 = (name_not_found ftv)
in (_116_699, (FStar_Ident.range_of_lid ftv)))
in FStar_Absyn_Syntax.Error (_116_700))
in (Prims.raise _116_701))
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
let _37_894 = env
in {solver = _37_894.solver; range = _37_894.range; curmodule = _37_894.curmodule; gamma = (Binding_sig (s))::env.gamma; modules = _37_894.modules; expected_typ = _37_894.expected_typ; level = _37_894.level; sigtab = _37_894.sigtab; is_pattern = _37_894.is_pattern; instantiate_targs = _37_894.instantiate_targs; instantiate_vargs = _37_894.instantiate_vargs; effects = _37_894.effects; generalize = _37_894.generalize; letrecs = _37_894.letrecs; top_level = _37_894.top_level; check_uvars = _37_894.check_uvars; use_eq = _37_894.use_eq; is_iface = _37_894.is_iface; admit = _37_894.admit; default_effects = _37_894.default_effects}) s))

# 578 "FStar.Tc.Env.fst"
let push_local_binding : env  ->  binding  ->  env = (fun env b -> (
# 578 "FStar.Tc.Env.fst"
let _37_898 = env
in {solver = _37_898.solver; range = _37_898.range; curmodule = _37_898.curmodule; gamma = (b)::env.gamma; modules = _37_898.modules; expected_typ = _37_898.expected_typ; level = _37_898.level; sigtab = _37_898.sigtab; is_pattern = _37_898.is_pattern; instantiate_targs = _37_898.instantiate_targs; instantiate_vargs = _37_898.instantiate_vargs; effects = _37_898.effects; generalize = _37_898.generalize; letrecs = _37_898.letrecs; top_level = _37_898.top_level; check_uvars = _37_898.check_uvars; use_eq = _37_898.use_eq; is_iface = _37_898.is_iface; admit = _37_898.admit; default_effects = _37_898.default_effects}))

# 580 "FStar.Tc.Env.fst"
let uvars_in_env : env  ->  FStar_Absyn_Syntax.uvars = (fun env -> (
# 581 "FStar.Tc.Env.fst"
let no_uvs = (let _116_718 = (FStar_Absyn_Syntax.new_uv_set ())
in (let _116_717 = (FStar_Absyn_Syntax.new_uvt_set ())
in (let _116_716 = (FStar_Absyn_Syntax.new_uvt_set ())
in {FStar_Absyn_Syntax.uvars_k = _116_718; FStar_Absyn_Syntax.uvars_t = _116_717; FStar_Absyn_Syntax.uvars_e = _116_716})))
in (
# 586 "FStar.Tc.Env.fst"
let ext = (fun out uvs -> (
# 587 "FStar.Tc.Env.fst"
let _37_905 = out
in (let _116_725 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_k uvs.FStar_Absyn_Syntax.uvars_k)
in (let _116_724 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_t uvs.FStar_Absyn_Syntax.uvars_t)
in (let _116_723 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_e uvs.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _116_725; FStar_Absyn_Syntax.uvars_t = _116_724; FStar_Absyn_Syntax.uvars_e = _116_723})))))
in (
# 590 "FStar.Tc.Env.fst"
let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_lid (_, t)::tl) | (Binding_var (_, t)::tl) -> begin
(let _116_731 = (let _116_730 = (FStar_Absyn_Util.uvars_in_typ t)
in (ext out _116_730))
in (aux _116_731 tl))
end
| Binding_typ (_37_925, k)::tl -> begin
(let _116_733 = (let _116_732 = (FStar_Absyn_Util.uvars_in_kind k)
in (ext out _116_732))
in (aux _116_733 tl))
end
| Binding_sig (_37_933)::_37_931 -> begin
out
end))
in (aux no_uvs env.gamma)))))

# 598 "FStar.Tc.Env.fst"
let push_module : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env m -> (
# 599 "FStar.Tc.Env.fst"
let _37_938 = (add_sigelts env m.FStar_Absyn_Syntax.exports)
in (
# 600 "FStar.Tc.Env.fst"
let _37_940 = env
in {solver = _37_940.solver; range = _37_940.range; curmodule = _37_940.curmodule; gamma = []; modules = (m)::env.modules; expected_typ = None; level = _37_940.level; sigtab = _37_940.sigtab; is_pattern = _37_940.is_pattern; instantiate_targs = _37_940.instantiate_targs; instantiate_vargs = _37_940.instantiate_vargs; effects = _37_940.effects; generalize = _37_940.generalize; letrecs = _37_940.letrecs; top_level = _37_940.top_level; check_uvars = _37_940.check_uvars; use_eq = _37_940.use_eq; is_iface = _37_940.is_iface; admit = _37_940.admit; default_effects = _37_940.default_effects})))

# 605 "FStar.Tc.Env.fst"
let set_expected_typ : env  ->  FStar_Absyn_Syntax.typ  ->  env = (fun env t -> (match (t) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const ({FStar_Absyn_Syntax.v = _37_965; FStar_Absyn_Syntax.sort = {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _37_961; FStar_Absyn_Syntax.pos = _37_959; FStar_Absyn_Syntax.fvs = _37_957; FStar_Absyn_Syntax.uvs = _37_955}; FStar_Absyn_Syntax.p = _37_953}); FStar_Absyn_Syntax.tk = _37_951; FStar_Absyn_Syntax.pos = _37_949; FStar_Absyn_Syntax.fvs = _37_947; FStar_Absyn_Syntax.uvs = _37_945} -> begin
(let _116_743 = (let _116_742 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "Setting expected type to %s with kind unknown" _116_742))
in (FStar_All.failwith _116_743))
end
| _37_970 -> begin
(
# 608 "FStar.Tc.Env.fst"
let _37_971 = env
in {solver = _37_971.solver; range = _37_971.range; curmodule = _37_971.curmodule; gamma = _37_971.gamma; modules = _37_971.modules; expected_typ = Some (t); level = _37_971.level; sigtab = _37_971.sigtab; is_pattern = _37_971.is_pattern; instantiate_targs = _37_971.instantiate_targs; instantiate_vargs = _37_971.instantiate_vargs; effects = _37_971.effects; generalize = _37_971.generalize; letrecs = _37_971.letrecs; top_level = _37_971.top_level; check_uvars = _37_971.check_uvars; use_eq = false; is_iface = _37_971.is_iface; admit = _37_971.admit; default_effects = _37_971.default_effects})
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
let clear_expected_typ : env  ->  (env * FStar_Absyn_Syntax.typ Prims.option) = (fun env -> (let _116_748 = (expected_typ env)
in ((
# 613 "FStar.Tc.Env.fst"
let _37_978 = env
in {solver = _37_978.solver; range = _37_978.range; curmodule = _37_978.curmodule; gamma = _37_978.gamma; modules = _37_978.modules; expected_typ = None; level = _37_978.level; sigtab = _37_978.sigtab; is_pattern = _37_978.is_pattern; instantiate_targs = _37_978.instantiate_targs; instantiate_vargs = _37_978.instantiate_vargs; effects = _37_978.effects; generalize = _37_978.generalize; letrecs = _37_978.letrecs; top_level = _37_978.top_level; check_uvars = _37_978.check_uvars; use_eq = false; is_iface = _37_978.is_iface; admit = _37_978.admit; default_effects = _37_978.default_effects}), _116_748)))

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
(let _116_766 = (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_116_766)::out)
end
| Binding_typ (a, k) -> begin
(let _116_767 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_116_767)::out)
end
| _37_1002 -> begin
out
end)) [] env.gamma))

# 627 "FStar.Tc.Env.fst"
let t_binders : env  ->  FStar_Absyn_Syntax.binders = (fun env -> (FStar_List.fold_left (fun out b -> (match (b) with
| Binding_var (_37_1007) -> begin
out
end
| Binding_typ (a, k) -> begin
(let _116_772 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_116_772)::out)
end
| _37_1014 -> begin
out
end)) [] env.gamma))

# 633 "FStar.Tc.Env.fst"
let idents : env  ->  FStar_Absyn_Syntax.freevars = (fun env -> (let _116_776 = (let _116_775 = (binders env)
in (FStar_All.pipe_right _116_775 (FStar_List.map Prims.fst)))
in (FStar_Absyn_Syntax.freevars_of_list _116_776)))

# 635 "FStar.Tc.Env.fst"
let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (
# 636 "FStar.Tc.Env.fst"
let keys = (FStar_List.fold_left (fun keys _37_13 -> (match (_37_13) with
| Binding_sig (s) -> begin
(let _116_781 = (FStar_Absyn_Util.lids_of_sigelt s)
in (FStar_List.append _116_781 keys))
end
| _37_1022 -> begin
keys
end)) [] env.gamma)
in (let _116_786 = (sigtab env)
in (FStar_Util.smap_fold _116_786 (fun _37_1024 v keys -> (let _116_785 = (FStar_Absyn_Util.lids_of_sigelt v)
in (FStar_List.append _116_785 keys))) keys))))




