
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
| Binding_var (_40_16) -> begin
_40_16
end))

# 30 "FStar.Tc.Env.fst"
let ___Binding_typ____0 = (fun projectee -> (match (projectee) with
| Binding_typ (_40_19) -> begin
_40_19
end))

# 31 "FStar.Tc.Env.fst"
let ___Binding_lid____0 = (fun projectee -> (match (projectee) with
| Binding_lid (_40_22) -> begin
_40_22
end))

# 32 "FStar.Tc.Env.fst"
let ___Binding_sig____0 = (fun projectee -> (match (projectee) with
| Binding_sig (_40_25) -> begin
_40_25
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
let _40_35 = (FStar_List.iter (fun se -> (
# 42 "FStar.Tc.Env.fst"
let lids = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (FStar_Util.smap_add ht l.FStar_Ident.str se)) lids))) s)
in ht)))

# 46 "FStar.Tc.Env.fst"
let modules_to_sigtables = (fun mods -> (let _133_65 = (FStar_List.collect (fun _40_41 -> (match (_40_41) with
| (_40_39, m) -> begin
m.FStar_Absyn_Syntax.declarations
end)) mods)
in (signature_to_sigtables _133_65)))

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

# 159 "FStar.Tc.Env.fst"
let bound_vars : env  ->  (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either Prims.list = (fun env -> (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _40_1 -> (match (_40_1) with
| Binding_typ (a, k) -> begin
(let _133_291 = (FStar_All.pipe_left (fun _133_290 -> FStar_Util.Inl (_133_290)) (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_133_291)::[])
end
| Binding_var (x, t) -> begin
(let _133_293 = (FStar_All.pipe_left (fun _133_292 -> FStar_Util.Inr (_133_292)) (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_133_293)::[])
end
| Binding_lid (_40_96) -> begin
[]
end
| Binding_sig (_40_99) -> begin
[]
end)))))

# 166 "FStar.Tc.Env.fst"
let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Absyn_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Absyn_Syntax.name l))))))

# 169 "FStar.Tc.Env.fst"
let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))

# 172 "FStar.Tc.Env.fst"
let new_sigtab = (fun _40_106 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))

# 173 "FStar.Tc.Env.fst"
let sigtab : env  ->  sigtable = (fun env -> (FStar_List.hd env.sigtab))

# 174 "FStar.Tc.Env.fst"
let push : env  ->  Prims.string  ->  env = (fun env msg -> (
# 175 "FStar.Tc.Env.fst"
let _40_110 = (env.solver.push msg)
in (
# 176 "FStar.Tc.Env.fst"
let _40_112 = env
in (let _133_312 = (let _133_311 = (let _133_310 = (sigtab env)
in (FStar_Util.smap_copy _133_310))
in (_133_311)::env.sigtab)
in {solver = _40_112.solver; range = _40_112.range; curmodule = _40_112.curmodule; gamma = _40_112.gamma; modules = _40_112.modules; expected_typ = _40_112.expected_typ; level = _40_112.level; sigtab = _133_312; is_pattern = _40_112.is_pattern; instantiate_targs = _40_112.instantiate_targs; instantiate_vargs = _40_112.instantiate_vargs; effects = _40_112.effects; generalize = _40_112.generalize; letrecs = _40_112.letrecs; top_level = _40_112.top_level; check_uvars = _40_112.check_uvars; use_eq = _40_112.use_eq; is_iface = _40_112.is_iface; admit = _40_112.admit; default_effects = _40_112.default_effects}))))

# 177 "FStar.Tc.Env.fst"
let mark : env  ->  env = (fun env -> (
# 178 "FStar.Tc.Env.fst"
let _40_115 = (env.solver.mark "USER MARK")
in (
# 179 "FStar.Tc.Env.fst"
let _40_117 = env
in (let _133_317 = (let _133_316 = (let _133_315 = (sigtab env)
in (FStar_Util.smap_copy _133_315))
in (_133_316)::env.sigtab)
in {solver = _40_117.solver; range = _40_117.range; curmodule = _40_117.curmodule; gamma = _40_117.gamma; modules = _40_117.modules; expected_typ = _40_117.expected_typ; level = _40_117.level; sigtab = _133_317; is_pattern = _40_117.is_pattern; instantiate_targs = _40_117.instantiate_targs; instantiate_vargs = _40_117.instantiate_vargs; effects = _40_117.effects; generalize = _40_117.generalize; letrecs = _40_117.letrecs; top_level = _40_117.top_level; check_uvars = _40_117.check_uvars; use_eq = _40_117.use_eq; is_iface = _40_117.is_iface; admit = _40_117.admit; default_effects = _40_117.default_effects}))))

# 180 "FStar.Tc.Env.fst"
let commit_mark : env  ->  env = (fun env -> (
# 181 "FStar.Tc.Env.fst"
let _40_120 = (env.solver.commit_mark "USER MARK")
in (
# 182 "FStar.Tc.Env.fst"
let sigtab = (match (env.sigtab) with
| (hd)::(_40_124)::tl -> begin
(hd)::tl
end
| _40_129 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 185 "FStar.Tc.Env.fst"
let _40_131 = env
in {solver = _40_131.solver; range = _40_131.range; curmodule = _40_131.curmodule; gamma = _40_131.gamma; modules = _40_131.modules; expected_typ = _40_131.expected_typ; level = _40_131.level; sigtab = sigtab; is_pattern = _40_131.is_pattern; instantiate_targs = _40_131.instantiate_targs; instantiate_vargs = _40_131.instantiate_vargs; effects = _40_131.effects; generalize = _40_131.generalize; letrecs = _40_131.letrecs; top_level = _40_131.top_level; check_uvars = _40_131.check_uvars; use_eq = _40_131.use_eq; is_iface = _40_131.is_iface; admit = _40_131.admit; default_effects = _40_131.default_effects}))))

# 186 "FStar.Tc.Env.fst"
let reset_mark : env  ->  env = (fun env -> (
# 187 "FStar.Tc.Env.fst"
let _40_134 = (env.solver.reset_mark "USER MARK")
in (
# 188 "FStar.Tc.Env.fst"
let _40_136 = env
in (let _133_322 = (FStar_List.tl env.sigtab)
in {solver = _40_136.solver; range = _40_136.range; curmodule = _40_136.curmodule; gamma = _40_136.gamma; modules = _40_136.modules; expected_typ = _40_136.expected_typ; level = _40_136.level; sigtab = _133_322; is_pattern = _40_136.is_pattern; instantiate_targs = _40_136.instantiate_targs; instantiate_vargs = _40_136.instantiate_vargs; effects = _40_136.effects; generalize = _40_136.generalize; letrecs = _40_136.letrecs; top_level = _40_136.top_level; check_uvars = _40_136.check_uvars; use_eq = _40_136.use_eq; is_iface = _40_136.is_iface; admit = _40_136.admit; default_effects = _40_136.default_effects}))))

# 189 "FStar.Tc.Env.fst"
let pop : env  ->  Prims.string  ->  env = (fun env msg -> (match (env.sigtab) with
| ([]) | ((_)::[]) -> begin
(FStar_All.failwith "Too many pops")
end
| (_40_146)::tl -> begin
(
# 193 "FStar.Tc.Env.fst"
let _40_148 = (env.solver.pop msg)
in (
# 194 "FStar.Tc.Env.fst"
let _40_150 = env
in {solver = _40_150.solver; range = _40_150.range; curmodule = _40_150.curmodule; gamma = _40_150.gamma; modules = _40_150.modules; expected_typ = _40_150.expected_typ; level = _40_150.level; sigtab = tl; is_pattern = _40_150.is_pattern; instantiate_targs = _40_150.instantiate_targs; instantiate_vargs = _40_150.instantiate_vargs; effects = _40_150.effects; generalize = _40_150.generalize; letrecs = _40_150.letrecs; top_level = _40_150.top_level; check_uvars = _40_150.check_uvars; use_eq = _40_150.use_eq; is_iface = _40_150.is_iface; admit = _40_150.admit; default_effects = _40_150.default_effects}))
end))

# 196 "FStar.Tc.Env.fst"
let initial_env : solver_t  ->  FStar_Ident.lident  ->  env = (fun solver module_lid -> (let _133_332 = (let _133_331 = (new_sigtab ())
in (_133_331)::[])
in {solver = solver; range = FStar_Absyn_Syntax.dummyRange; curmodule = module_lid; gamma = []; modules = []; expected_typ = None; level = Expr; sigtab = _133_332; is_pattern = false; instantiate_targs = true; instantiate_vargs = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = true; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []}))

# 220 "FStar.Tc.Env.fst"
let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Absyn_Syntax.mname l)))))

# 223 "FStar.Tc.Env.fst"
let name_not_found : FStar_Absyn_Syntax.lident  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))

# 226 "FStar.Tc.Env.fst"
let variable_not_found = (fun v -> (let _133_341 = (FStar_Absyn_Print.strBvd v)
in (FStar_Util.format1 "Variable \"%s\" not found" _133_341)))

# 229 "FStar.Tc.Env.fst"
let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _133_348 = (let _133_347 = (let _133_346 = (name_not_found l)
in ((_133_346), ((FStar_Ident.range_of_lid l))))
in FStar_Absyn_Syntax.Error (_133_347))
in (Prims.raise _133_348))
end
| Some (md) -> begin
md
end))

# 234 "FStar.Tc.Env.fst"
let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
((l1), ((fun t wp -> wp)), ((fun t wp -> wp)))
end else begin
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _40_179 -> (match (_40_179) with
| (m1, m2, _40_174, _40_176, _40_178) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _133_404 = (let _133_403 = (let _133_402 = (let _133_401 = (FStar_Absyn_Print.sli l1)
in (let _133_400 = (FStar_Absyn_Print.sli l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _133_401 _133_400)))
in ((_133_402), (env.range)))
in FStar_Absyn_Syntax.Error (_133_403))
in (Prims.raise _133_404))
end
| Some (_40_182, _40_184, m3, j1, j2) -> begin
((m3), (j1), (j2))
end)
end)

# 241 "FStar.Tc.Env.fst"
let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge Prims.option = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end else begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end)

# 246 "FStar.Tc.Env.fst"
let wp_sig_aux : FStar_Absyn_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) = (fun decls m -> (match ((FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Absyn_Syntax.mname m))))) with
| None -> begin
(let _133_419 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _133_419))
end
| Some (md) -> begin
(match (md.FStar_Absyn_Syntax.signature.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (((FStar_Util.Inl (a), _40_215))::((FStar_Util.Inl (wp), _40_210))::((FStar_Util.Inl (wlp), _40_205))::[], {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_effect; FStar_Absyn_Syntax.tk = _40_225; FStar_Absyn_Syntax.pos = _40_223; FStar_Absyn_Syntax.fvs = _40_221; FStar_Absyn_Syntax.uvs = _40_219}) -> begin
((a), (wp.FStar_Absyn_Syntax.sort))
end
| _40_231 -> begin
(FStar_All.failwith "Impossible")
end)
end))

# 254 "FStar.Tc.Env.fst"
let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.btvar * FStar_Absyn_Syntax.knd) = (fun env m -> (wp_sig_aux env.effects.decls m))

# 256 "FStar.Tc.Env.fst"
let default_effect : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (FStar_Util.find_map env.default_effects (fun _40_238 -> (match (_40_238) with
| (l', m) -> begin
if (FStar_Ident.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))

# 258 "FStar.Tc.Env.fst"
let build_lattice : env  ->  FStar_Absyn_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Absyn_Syntax.Sig_effect_abbrev (l, _40_243, c, quals, r) -> begin
(match ((FStar_Util.find_map quals (fun _40_2 -> (match (_40_2) with
| FStar_Absyn_Syntax.DefaultEffect (n) -> begin
n
end
| _40_253 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(
# 262 "FStar.Tc.Env.fst"
let _40_257 = env
in {solver = _40_257.solver; range = _40_257.range; curmodule = _40_257.curmodule; gamma = _40_257.gamma; modules = _40_257.modules; expected_typ = _40_257.expected_typ; level = _40_257.level; sigtab = _40_257.sigtab; is_pattern = _40_257.is_pattern; instantiate_targs = _40_257.instantiate_targs; instantiate_vargs = _40_257.instantiate_vargs; effects = _40_257.effects; generalize = _40_257.generalize; letrecs = _40_257.letrecs; top_level = _40_257.top_level; check_uvars = _40_257.check_uvars; use_eq = _40_257.use_eq; is_iface = _40_257.is_iface; admit = _40_257.admit; default_effects = (((e), (l)))::env.default_effects})
end)
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, _40_261) -> begin
(
# 265 "FStar.Tc.Env.fst"
let effects = (
# 265 "FStar.Tc.Env.fst"
let _40_264 = env.effects
in {decls = (ne)::env.effects.decls; order = _40_264.order; joins = _40_264.joins})
in (
# 266 "FStar.Tc.Env.fst"
let _40_267 = env
in {solver = _40_267.solver; range = _40_267.range; curmodule = _40_267.curmodule; gamma = _40_267.gamma; modules = _40_267.modules; expected_typ = _40_267.expected_typ; level = _40_267.level; sigtab = _40_267.sigtab; is_pattern = _40_267.is_pattern; instantiate_targs = _40_267.instantiate_targs; instantiate_vargs = _40_267.instantiate_vargs; effects = effects; generalize = _40_267.generalize; letrecs = _40_267.letrecs; top_level = _40_267.top_level; check_uvars = _40_267.check_uvars; use_eq = _40_267.use_eq; is_iface = _40_267.is_iface; admit = _40_267.admit; default_effects = _40_267.default_effects}))
end
| FStar_Absyn_Syntax.Sig_sub_effect (sub, _40_271) -> begin
(
# 269 "FStar.Tc.Env.fst"
let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _133_440 = (e1.mlift r wp1)
in (e2.mlift r _133_440)))})
in (
# 274 "FStar.Tc.Env.fst"
let mk_lift = (fun lift_t r wp1 -> (let _133_451 = (let _133_450 = (let _133_449 = (FStar_Absyn_Syntax.targ r)
in (let _133_448 = (let _133_447 = (FStar_Absyn_Syntax.targ wp1)
in (_133_447)::[])
in (_133_449)::_133_448))
in ((lift_t), (_133_450)))
in (FStar_Absyn_Syntax.mk_Typ_app _133_451 None wp1.FStar_Absyn_Syntax.pos)))
in (
# 276 "FStar.Tc.Env.fst"
let edge = {msource = sub.FStar_Absyn_Syntax.source; mtarget = sub.FStar_Absyn_Syntax.target; mlift = (mk_lift sub.FStar_Absyn_Syntax.lift)}
in (
# 280 "FStar.Tc.Env.fst"
let id_edge = (fun l -> {msource = sub.FStar_Absyn_Syntax.source; mtarget = sub.FStar_Absyn_Syntax.target; mlift = (fun t wp -> wp)})
in (
# 285 "FStar.Tc.Env.fst"
let print_mlift = (fun l -> (
# 286 "FStar.Tc.Env.fst"
let arg = (let _133_468 = (FStar_Absyn_Syntax.lid_of_path (("ARG")::[]) FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Util.ftv _133_468 FStar_Absyn_Syntax.mk_Kind_type))
in (
# 287 "FStar.Tc.Env.fst"
let wp = (let _133_469 = (FStar_Absyn_Syntax.lid_of_path (("WP")::[]) FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Util.ftv _133_469 FStar_Absyn_Syntax.mk_Kind_unknown))
in (let _133_470 = (l arg wp)
in (FStar_Absyn_Print.typ_to_string _133_470)))))
in (
# 289 "FStar.Tc.Env.fst"
let order = (edge)::env.effects.order
in (
# 291 "FStar.Tc.Env.fst"
let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Absyn_Syntax.mname)))
in (
# 293 "FStar.Tc.Env.fst"
let find_edge = (fun order _40_299 -> (match (_40_299) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _133_476 -> Some (_133_476)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (
# 302 "FStar.Tc.Env.fst"
let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _133_484 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _133_483 = (find_edge order ((i), (k)))
in (let _133_482 = (find_edge order ((k), (j)))
in ((_133_483), (_133_482))))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _40_311 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _133_484))) order))
in (
# 313 "FStar.Tc.Env.fst"
let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (
# 315 "FStar.Tc.Env.fst"
let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (
# 318 "FStar.Tc.Env.fst"
let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _133_492 = (find_edge order ((i), (k)))
in (let _133_491 = (find_edge order ((j), (k)))
in ((_133_492), (_133_491))))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some (((k), (ik), (jk)))
end
| Some (ub, _40_328, _40_330) -> begin
if ((let _133_493 = (find_edge order ((k), (ub)))
in (FStar_Util.is_some _133_493)) && (not ((let _133_494 = (find_edge order ((ub), (k)))
in (FStar_Util.is_some _133_494))))) then begin
Some (((k), (ik), (jk)))
end else begin
bopt
end
end)
end
| _40_334 -> begin
bopt
end)) None))
in (match (join_opt) with
| None -> begin
[]
end
| Some (k, e1, e2) -> begin
(((i), (j), (k), (e1.mlift), (e2.mlift)))::[]
end))))))))
in (
# 335 "FStar.Tc.Env.fst"
let effects = (
# 335 "FStar.Tc.Env.fst"
let _40_343 = env.effects
in {decls = _40_343.decls; order = order; joins = joins})
in (
# 338 "FStar.Tc.Env.fst"
let _40_346 = env
in {solver = _40_346.solver; range = _40_346.range; curmodule = _40_346.curmodule; gamma = _40_346.gamma; modules = _40_346.modules; expected_typ = _40_346.expected_typ; level = _40_346.level; sigtab = _40_346.sigtab; is_pattern = _40_346.is_pattern; instantiate_targs = _40_346.instantiate_targs; instantiate_vargs = _40_346.instantiate_vargs; effects = effects; generalize = _40_346.generalize; letrecs = _40_346.letrecs; top_level = _40_346.top_level; check_uvars = _40_346.check_uvars; use_eq = _40_346.use_eq; is_iface = _40_346.is_iface; admit = _40_346.admit; default_effects = _40_346.default_effects})))))))))))))
end
| _40_349 -> begin
env
end))

# 343 "FStar.Tc.Env.fst"
let rec add_sigelt : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Absyn_Syntax.Sig_bundle (ses, _40_354, _40_356, _40_358) -> begin
(add_sigelts env ses)
end
| _40_362 -> begin
(
# 346 "FStar.Tc.Env.fst"
let lids = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _133_502 = (sigtab env)
in (FStar_Util.smap_add _133_502 l.FStar_Ident.str se))) lids))
end))
and add_sigelts : env  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))

# 352 "FStar.Tc.Env.fst"
let empty_lid : FStar_Absyn_Syntax.lident = (let _133_506 = (let _133_505 = (FStar_Absyn_Syntax.id_of_text "")
in (_133_505)::[])
in (FStar_Absyn_Syntax.lid_of_ids _133_506))

# 354 "FStar.Tc.Env.fst"
let finish_module : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env m -> (
# 355 "FStar.Tc.Env.fst"
let sigs = if (FStar_Ident.lid_equals m.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid) then begin
(FStar_All.pipe_right env.gamma (FStar_List.collect (fun _40_3 -> (match (_40_3) with
| Binding_sig (se) -> begin
(se)::[]
end
| _40_373 -> begin
[]
end))))
end else begin
m.FStar_Absyn_Syntax.exports
end
in (
# 361 "FStar.Tc.Env.fst"
let _40_375 = (add_sigelts env sigs)
in (
# 362 "FStar.Tc.Env.fst"
let _40_377 = env
in {solver = _40_377.solver; range = _40_377.range; curmodule = empty_lid; gamma = []; modules = (m)::env.modules; expected_typ = _40_377.expected_typ; level = _40_377.level; sigtab = _40_377.sigtab; is_pattern = _40_377.is_pattern; instantiate_targs = _40_377.instantiate_targs; instantiate_vargs = _40_377.instantiate_vargs; effects = _40_377.effects; generalize = _40_377.generalize; letrecs = _40_377.letrecs; top_level = _40_377.top_level; check_uvars = _40_377.check_uvars; use_eq = _40_377.use_eq; is_iface = _40_377.is_iface; admit = _40_377.admit; default_effects = _40_377.default_effects}))))

# 368 "FStar.Tc.Env.fst"
let set_level : env  ->  level  ->  env = (fun env level -> (
# 368 "FStar.Tc.Env.fst"
let _40_381 = env
in {solver = _40_381.solver; range = _40_381.range; curmodule = _40_381.curmodule; gamma = _40_381.gamma; modules = _40_381.modules; expected_typ = _40_381.expected_typ; level = level; sigtab = _40_381.sigtab; is_pattern = _40_381.is_pattern; instantiate_targs = _40_381.instantiate_targs; instantiate_vargs = _40_381.instantiate_vargs; effects = _40_381.effects; generalize = _40_381.generalize; letrecs = _40_381.letrecs; top_level = _40_381.top_level; check_uvars = _40_381.check_uvars; use_eq = _40_381.use_eq; is_iface = _40_381.is_iface; admit = _40_381.admit; default_effects = _40_381.default_effects}))

# 369 "FStar.Tc.Env.fst"
let is_level : env  ->  level  ->  Prims.bool = (fun env level -> (env.level = level))

# 370 "FStar.Tc.Env.fst"
let modules : env  ->  FStar_Absyn_Syntax.modul Prims.list = (fun env -> env.modules)

# 371 "FStar.Tc.Env.fst"
let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)

# 372 "FStar.Tc.Env.fst"
let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (
# 372 "FStar.Tc.Env.fst"
let _40_389 = env
in {solver = _40_389.solver; range = _40_389.range; curmodule = lid; gamma = _40_389.gamma; modules = _40_389.modules; expected_typ = _40_389.expected_typ; level = _40_389.level; sigtab = _40_389.sigtab; is_pattern = _40_389.is_pattern; instantiate_targs = _40_389.instantiate_targs; instantiate_vargs = _40_389.instantiate_vargs; effects = _40_389.effects; generalize = _40_389.generalize; letrecs = _40_389.letrecs; top_level = _40_389.top_level; check_uvars = _40_389.check_uvars; use_eq = _40_389.use_eq; is_iface = _40_389.is_iface; admit = _40_389.admit; default_effects = _40_389.default_effects}))

# 373 "FStar.Tc.Env.fst"
let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Absyn_Syntax.dummyRange) then begin
e
end else begin
(
# 373 "FStar.Tc.Env.fst"
let _40_393 = e
in {solver = _40_393.solver; range = r; curmodule = _40_393.curmodule; gamma = _40_393.gamma; modules = _40_393.modules; expected_typ = _40_393.expected_typ; level = _40_393.level; sigtab = _40_393.sigtab; is_pattern = _40_393.is_pattern; instantiate_targs = _40_393.instantiate_targs; instantiate_vargs = _40_393.instantiate_vargs; effects = _40_393.effects; generalize = _40_393.generalize; letrecs = _40_393.letrecs; top_level = _40_393.top_level; check_uvars = _40_393.check_uvars; use_eq = _40_393.use_eq; is_iface = _40_393.is_iface; admit = _40_393.admit; default_effects = _40_393.default_effects})
end)

# 374 "FStar.Tc.Env.fst"
let get_range : env  ->  FStar_Range.range = (fun e -> e.range)

# 375 "FStar.Tc.Env.fst"
let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.sigelt Prims.option = (fun env lid -> (let _133_538 = (sigtab env)
in (FStar_Util.smap_try_find _133_538 (FStar_Ident.text_of_lid lid))))

# 377 "FStar.Tc.Env.fst"
let lookup_bvvdef : env  ->  FStar_Absyn_Syntax.bvvdef  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env bvvd -> (FStar_Util.find_map env.gamma (fun _40_4 -> (match (_40_4) with
| Binding_var (id, t) when (FStar_Absyn_Util.bvd_eq id bvvd) -> begin
Some (t)
end
| _40_406 -> begin
None
end))))

# 382 "FStar.Tc.Env.fst"
let lookup_bvar : env  ->  FStar_Absyn_Syntax.bvvar  ->  FStar_Absyn_Syntax.typ = (fun env bv -> (match ((lookup_bvvdef env bv.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _133_550 = (let _133_549 = (let _133_548 = (variable_not_found bv.FStar_Absyn_Syntax.v)
in ((_133_548), ((FStar_Absyn_Util.range_of_bvd bv.FStar_Absyn_Syntax.v))))
in FStar_Absyn_Syntax.Error (_133_549))
in (Prims.raise _133_550))
end
| Some (t) -> begin
t
end))

# 387 "FStar.Tc.Env.fst"
let in_cur_mod : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 388 "FStar.Tc.Env.fst"
let cur = (current_module env)
in if (l.FStar_Ident.nsstr = cur.FStar_Ident.str) then begin
true
end else begin
if (FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str) then begin
(
# 391 "FStar.Tc.Env.fst"
let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (
# 392 "FStar.Tc.Env.fst"
let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (
# 393 "FStar.Tc.Env.fst"
let rec aux = (fun c l -> (match (((c), (l))) with
| ([], _40_422) -> begin
true
end
| (_40_425, []) -> begin
false
end
| ((hd)::tl, (hd')::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _40_436 -> begin
false
end))
in (aux cur lns))))
end else begin
false
end
end))

# 401 "FStar.Tc.Env.fst"
let lookup_qname : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.sigelt) FStar_Util.either Prims.option = (fun env lid -> (
# 402 "FStar.Tc.Env.fst"
let cur_mod = (in_cur_mod env lid)
in (
# 403 "FStar.Tc.Env.fst"
let found = if cur_mod then begin
(FStar_Util.find_map env.gamma (fun _40_5 -> (match (_40_5) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
Some (FStar_Util.Inl (t))
end else begin
None
end
end
| Binding_sig (FStar_Absyn_Syntax.Sig_bundle (ses, _40_447, _40_449, _40_451)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _133_565 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _133_565 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
Some (FStar_Util.Inr (se))
end else begin
None
end))
end
| Binding_sig (s) -> begin
(
# 412 "FStar.Tc.Env.fst"
let lids = (FStar_Absyn_Util.lids_of_sigelt s)
in if (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals lid))) then begin
Some (FStar_Util.Inr (s))
end else begin
None
end)
end
| _40_460 -> begin
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

# 424 "FStar.Tc.Env.fst"
let lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_40_468, t, (_40_471, tps, _40_474), _40_477, _40_479, _40_481))) -> begin
(let _133_571 = (FStar_List.map (fun _40_489 -> (match (_40_489) with
| (x, _40_488) -> begin
((x), (Some (FStar_Absyn_Syntax.Implicit (true))))
end)) tps)
in (FStar_Absyn_Util.close_typ _133_571 t))
end
| _40_491 -> begin
(let _133_574 = (let _133_573 = (let _133_572 = (name_not_found lid)
in ((_133_572), ((FStar_Ident.range_of_lid lid))))
in FStar_Absyn_Syntax.Error (_133_573))
in (Prims.raise _133_574))
end))

# 430 "FStar.Tc.Env.fst"
let lookup_kind_abbrev : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_kind_abbrev (l, binders, k, _40_498))) -> begin
((l), (binders), (k))
end
| _40_504 -> begin
(let _133_581 = (let _133_580 = (let _133_579 = (name_not_found lid)
in ((_133_579), ((FStar_Ident.range_of_lid lid))))
in FStar_Absyn_Syntax.Error (_133_580))
in (Prims.raise _133_581))
end))

# 435 "FStar.Tc.Env.fst"
let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (
# 436 "FStar.Tc.Env.fst"
let fail = (fun _40_509 -> (match (()) with
| () -> begin
(let _133_592 = (let _133_591 = (FStar_Util.string_of_int i)
in (let _133_590 = (FStar_Absyn_Print.sli lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _133_591 _133_590)))
in (FStar_All.failwith _133_592))
end))
in (
# 437 "FStar.Tc.Env.fst"
let t = (lookup_datacon env lid)
in (match ((let _133_593 = (FStar_Absyn_Util.compress_typ t)
in _133_593.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, _40_513) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(
# 442 "FStar.Tc.Env.fst"
let b = (FStar_List.nth binders i)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _133_594 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (FStar_All.pipe_right _133_594 Prims.fst))
end
| FStar_Util.Inr (x) -> begin
(let _133_595 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (FStar_All.pipe_right _133_595 Prims.fst))
end))
end
end
| _40_522 -> begin
(fail ())
end))))

# 449 "FStar.Tc.Env.fst"
let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_40_526, t, q, _40_530))) -> begin
Some (((t), (q)))
end
| _40_536 -> begin
None
end))

# 454 "FStar.Tc.Env.fst"
let lookup_val_decl : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_40_540, t, _40_543, _40_545))) -> begin
t
end
| _40_551 -> begin
(let _133_606 = (let _133_605 = (let _133_604 = (name_not_found lid)
in ((_133_604), ((FStar_Ident.range_of_lid lid))))
in FStar_Absyn_Syntax.Error (_133_605))
in (Prims.raise _133_606))
end))

# 459 "FStar.Tc.Env.fst"
let lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ = (fun env lid -> (
# 460 "FStar.Tc.Env.fst"
let not_found = (fun _40_555 -> (match (()) with
| () -> begin
(let _133_615 = (let _133_614 = (let _133_613 = (name_not_found lid)
in ((_133_613), ((FStar_Ident.range_of_lid lid))))
in FStar_Absyn_Syntax.Error (_133_614))
in (Prims.raise _133_615))
end))
in (
# 463 "FStar.Tc.Env.fst"
let mapper = (fun _40_6 -> (match (_40_6) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_40_558, t, (_40_561, tps, _40_564), _40_567, _40_569, _40_571)) -> begin
(let _133_620 = (let _133_619 = (FStar_List.map (fun _40_578 -> (match (_40_578) with
| (x, _40_577) -> begin
((x), (Some (FStar_Absyn_Syntax.Implicit (true))))
end)) tps)
in (FStar_Absyn_Util.close_typ _133_619 t))
in Some (_133_620))
end
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (l, t, qs, _40_585)) -> begin
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
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_let ((_40_590, ({FStar_Absyn_Syntax.lbname = _40_597; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _40_594; FStar_Absyn_Syntax.lbdef = _40_592})::[]), _40_602, _40_604, _40_606)) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_let ((_40_611, lbs), _40_615, _40_617, _40_619)) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (_40_625) -> begin
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
in (match ((let _133_622 = (lookup_qname env lid)
in (FStar_Util.bind_opt _133_622 mapper))) with
| Some (t) -> begin
(
# 486 "FStar.Tc.Env.fst"
let _40_633 = t
in (let _133_623 = (FStar_Absyn_Syntax.range_of_lid lid)
in {FStar_Absyn_Syntax.n = _40_633.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _40_633.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = _133_623; FStar_Absyn_Syntax.fvs = _40_633.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _40_633.FStar_Absyn_Syntax.uvs}))
end
| None -> begin
(not_found ())
end))))

# 490 "FStar.Tc.Env.fst"
let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_40_639, _40_641, quals, _40_644))) -> begin
(FStar_All.pipe_right quals (FStar_Util.for_some (fun _40_7 -> (match (_40_7) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _40_652 -> begin
false
end))))
end
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_40_654, t, _40_657, _40_659, _40_661, _40_663))) -> begin
true
end
| _40_669 -> begin
false
end))

# 496 "FStar.Tc.Env.fst"
let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_40_673, _40_675, _40_677, _40_679, _40_681, tags, _40_684))) -> begin
(FStar_Util.for_some (fun _40_8 -> (match (_40_8) with
| (FStar_Absyn_Syntax.RecordType (_)) | (FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _40_697 -> begin
false
end)) tags)
end
| _40_699 -> begin
false
end))

# 502 "FStar.Tc.Env.fst"
let lookup_datacons_of_typ : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.typ) Prims.list Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_40_703, _40_705, _40_707, _40_709, datas, _40_712, _40_714))) -> begin
(let _133_640 = (FStar_List.map (fun l -> (let _133_639 = (lookup_lid env l)
in ((l), (_133_639)))) datas)
in Some (_133_640))
end
| _40_721 -> begin
None
end))

# 507 "FStar.Tc.Env.fst"
let lookup_effect_abbrev : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.comp) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, binders, c, quals, _40_729))) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _40_9 -> (match (_40_9) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _40_737 -> begin
false
end)))) then begin
None
end else begin
Some (((binders), (c)))
end
end
| _40_739 -> begin
None
end))

# 515 "FStar.Tc.Env.fst"
let lookup_typ_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _40_745, t, quals, _40_749))) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _40_10 -> (match (_40_10) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _40_757 -> begin
false
end)))) then begin
None
end else begin
(
# 520 "FStar.Tc.Env.fst"
let t = (FStar_Absyn_Util.close_with_lam tps t)
in (let _133_651 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named (((t), (lid)))))
in Some (_133_651)))
end
end
| _40_760 -> begin
None
end))

# 524 "FStar.Tc.Env.fst"
let lookup_opaque_typ_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _40_766, t, quals, _40_770))) -> begin
(
# 527 "FStar.Tc.Env.fst"
let t = (FStar_Absyn_Util.close_with_lam tps t)
in (let _133_656 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named (((t), (lid)))))
in Some (_133_656)))
end
| _40_777 -> begin
None
end))

# 531 "FStar.Tc.Env.fst"
let lookup_btvdef : env  ->  FStar_Absyn_Syntax.btvdef  ->  FStar_Absyn_Syntax.knd Prims.option = (fun env btvd -> (FStar_Util.find_map env.gamma (fun _40_11 -> (match (_40_11) with
| Binding_typ (id, k) when (FStar_Absyn_Util.bvd_eq id btvd) -> begin
Some (k)
end
| _40_786 -> begin
None
end))))

# 536 "FStar.Tc.Env.fst"
let lookup_btvar : env  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Absyn_Syntax.knd = (fun env btv -> (match ((lookup_btvdef env btv.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _133_668 = (let _133_667 = (let _133_666 = (variable_not_found btv.FStar_Absyn_Syntax.v)
in ((_133_666), ((FStar_Absyn_Util.range_of_bvd btv.FStar_Absyn_Syntax.v))))
in FStar_Absyn_Syntax.Error (_133_667))
in (Prims.raise _133_668))
end
| Some (k) -> begin
k
end))

# 541 "FStar.Tc.Env.fst"
let lookup_typ_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd = (fun env ftv -> (match ((lookup_qname env ftv)) with
| (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _, _, _, _)))) | (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, _, _, _)))) -> begin
(FStar_Absyn_Util.close_kind tps k)
end
| _40_820 -> begin
(let _133_675 = (let _133_674 = (let _133_673 = (name_not_found ftv)
in ((_133_673), ((FStar_Ident.range_of_lid ftv))))
in FStar_Absyn_Syntax.Error (_133_674))
in (Prims.raise _133_675))
end))

# 549 "FStar.Tc.Env.fst"
let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_, _, _, _, _, quals, _)))) | (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_, _, quals, _)))) -> begin
(FStar_Util.for_some (fun _40_12 -> (match (_40_12) with
| FStar_Absyn_Syntax.Projector (_40_852) -> begin
true
end
| _40_855 -> begin
false
end)) quals)
end
| _40_857 -> begin
false
end))

# 556 "FStar.Tc.Env.fst"
let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_new_effect (ne, _40_862))) -> begin
(let _133_686 = (FStar_Absyn_Util.close_kind ne.FStar_Absyn_Syntax.binders ne.FStar_Absyn_Syntax.signature)
in (FStar_All.pipe_right _133_686 (fun _133_685 -> Some (_133_685))))
end
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, binders, _40_870, _40_872, _40_874))) -> begin
(let _133_688 = (FStar_Absyn_Util.close_kind binders FStar_Absyn_Syntax.mk_Kind_effect)
in (FStar_All.pipe_right _133_688 (fun _133_687 -> Some (_133_687))))
end
| _40_880 -> begin
None
end))

# 565 "FStar.Tc.Env.fst"
let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _133_695 = (let _133_694 = (let _133_693 = (name_not_found ftv)
in ((_133_693), ((FStar_Ident.range_of_lid ftv))))
in FStar_Absyn_Syntax.Error (_133_694))
in (Prims.raise _133_695))
end
| Some (k) -> begin
k
end))

# 570 "FStar.Tc.Env.fst"
let lookup_operator : env  ->  FStar_Ident.ident  ->  FStar_Absyn_Syntax.typ = (fun env opname -> (
# 571 "FStar.Tc.Env.fst"
let primName = (FStar_Ident.lid_of_path (("Prims")::((Prims.strcat "_dummy_" opname.FStar_Ident.idText))::[]) FStar_Absyn_Syntax.dummyRange)
in (lookup_lid env primName)))

# 574 "FStar.Tc.Env.fst"
let push_sigelt : env  ->  FStar_Absyn_Syntax.sigelt  ->  env = (fun env s -> (build_lattice (
# 574 "FStar.Tc.Env.fst"
let _40_891 = env
in {solver = _40_891.solver; range = _40_891.range; curmodule = _40_891.curmodule; gamma = (Binding_sig (s))::env.gamma; modules = _40_891.modules; expected_typ = _40_891.expected_typ; level = _40_891.level; sigtab = _40_891.sigtab; is_pattern = _40_891.is_pattern; instantiate_targs = _40_891.instantiate_targs; instantiate_vargs = _40_891.instantiate_vargs; effects = _40_891.effects; generalize = _40_891.generalize; letrecs = _40_891.letrecs; top_level = _40_891.top_level; check_uvars = _40_891.check_uvars; use_eq = _40_891.use_eq; is_iface = _40_891.is_iface; admit = _40_891.admit; default_effects = _40_891.default_effects}) s))

# 575 "FStar.Tc.Env.fst"
let push_local_binding : env  ->  binding  ->  env = (fun env b -> (
# 575 "FStar.Tc.Env.fst"
let _40_895 = env
in {solver = _40_895.solver; range = _40_895.range; curmodule = _40_895.curmodule; gamma = (b)::env.gamma; modules = _40_895.modules; expected_typ = _40_895.expected_typ; level = _40_895.level; sigtab = _40_895.sigtab; is_pattern = _40_895.is_pattern; instantiate_targs = _40_895.instantiate_targs; instantiate_vargs = _40_895.instantiate_vargs; effects = _40_895.effects; generalize = _40_895.generalize; letrecs = _40_895.letrecs; top_level = _40_895.top_level; check_uvars = _40_895.check_uvars; use_eq = _40_895.use_eq; is_iface = _40_895.is_iface; admit = _40_895.admit; default_effects = _40_895.default_effects}))

# 577 "FStar.Tc.Env.fst"
let uvars_in_env : env  ->  FStar_Absyn_Syntax.uvars = (fun env -> (
# 578 "FStar.Tc.Env.fst"
let no_uvs = (let _133_712 = (FStar_Absyn_Syntax.new_uv_set ())
in (let _133_711 = (FStar_Absyn_Syntax.new_uvt_set ())
in (let _133_710 = (FStar_Absyn_Syntax.new_uvt_set ())
in {FStar_Absyn_Syntax.uvars_k = _133_712; FStar_Absyn_Syntax.uvars_t = _133_711; FStar_Absyn_Syntax.uvars_e = _133_710})))
in (
# 583 "FStar.Tc.Env.fst"
let ext = (fun out uvs -> (
# 584 "FStar.Tc.Env.fst"
let _40_902 = out
in (let _133_719 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_k uvs.FStar_Absyn_Syntax.uvars_k)
in (let _133_718 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_t uvs.FStar_Absyn_Syntax.uvars_t)
in (let _133_717 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_e uvs.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _133_719; FStar_Absyn_Syntax.uvars_t = _133_718; FStar_Absyn_Syntax.uvars_e = _133_717})))))
in (
# 587 "FStar.Tc.Env.fst"
let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| ((Binding_lid (_, t))::tl) | ((Binding_var (_, t))::tl) -> begin
(let _133_725 = (let _133_724 = (FStar_Absyn_Util.uvars_in_typ t)
in (ext out _133_724))
in (aux _133_725 tl))
end
| (Binding_typ (_40_922, k))::tl -> begin
(let _133_727 = (let _133_726 = (FStar_Absyn_Util.uvars_in_kind k)
in (ext out _133_726))
in (aux _133_727 tl))
end
| (Binding_sig (_40_930))::_40_928 -> begin
out
end))
in (aux no_uvs env.gamma)))))

# 595 "FStar.Tc.Env.fst"
let push_module : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env m -> (
# 596 "FStar.Tc.Env.fst"
let _40_935 = (add_sigelts env m.FStar_Absyn_Syntax.exports)
in (
# 597 "FStar.Tc.Env.fst"
let _40_937 = env
in {solver = _40_937.solver; range = _40_937.range; curmodule = _40_937.curmodule; gamma = []; modules = (m)::env.modules; expected_typ = None; level = _40_937.level; sigtab = _40_937.sigtab; is_pattern = _40_937.is_pattern; instantiate_targs = _40_937.instantiate_targs; instantiate_vargs = _40_937.instantiate_vargs; effects = _40_937.effects; generalize = _40_937.generalize; letrecs = _40_937.letrecs; top_level = _40_937.top_level; check_uvars = _40_937.check_uvars; use_eq = _40_937.use_eq; is_iface = _40_937.is_iface; admit = _40_937.admit; default_effects = _40_937.default_effects})))

# 602 "FStar.Tc.Env.fst"
let set_expected_typ : env  ->  FStar_Absyn_Syntax.typ  ->  env = (fun env t -> (match (t) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const ({FStar_Absyn_Syntax.v = _40_962; FStar_Absyn_Syntax.sort = {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _40_958; FStar_Absyn_Syntax.pos = _40_956; FStar_Absyn_Syntax.fvs = _40_954; FStar_Absyn_Syntax.uvs = _40_952}; FStar_Absyn_Syntax.p = _40_950}); FStar_Absyn_Syntax.tk = _40_948; FStar_Absyn_Syntax.pos = _40_946; FStar_Absyn_Syntax.fvs = _40_944; FStar_Absyn_Syntax.uvs = _40_942} -> begin
(let _133_737 = (let _133_736 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "Setting expected type to %s with kind unknown" _133_736))
in (FStar_All.failwith _133_737))
end
| _40_967 -> begin
(
# 605 "FStar.Tc.Env.fst"
let _40_968 = env
in {solver = _40_968.solver; range = _40_968.range; curmodule = _40_968.curmodule; gamma = _40_968.gamma; modules = _40_968.modules; expected_typ = Some (t); level = _40_968.level; sigtab = _40_968.sigtab; is_pattern = _40_968.is_pattern; instantiate_targs = _40_968.instantiate_targs; instantiate_vargs = _40_968.instantiate_vargs; effects = _40_968.effects; generalize = _40_968.generalize; letrecs = _40_968.letrecs; top_level = _40_968.top_level; check_uvars = _40_968.check_uvars; use_eq = false; is_iface = _40_968.is_iface; admit = _40_968.admit; default_effects = _40_968.default_effects})
end))

# 607 "FStar.Tc.Env.fst"
let expected_typ : env  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

# 610 "FStar.Tc.Env.fst"
let clear_expected_typ : env  ->  (env * FStar_Absyn_Syntax.typ Prims.option) = (fun env -> (let _133_742 = (expected_typ env)
in (((
# 610 "FStar.Tc.Env.fst"
let _40_975 = env
in {solver = _40_975.solver; range = _40_975.range; curmodule = _40_975.curmodule; gamma = _40_975.gamma; modules = _40_975.modules; expected_typ = None; level = _40_975.level; sigtab = _40_975.sigtab; is_pattern = _40_975.is_pattern; instantiate_targs = _40_975.instantiate_targs; instantiate_vargs = _40_975.instantiate_vargs; effects = _40_975.effects; generalize = _40_975.generalize; letrecs = _40_975.letrecs; top_level = _40_975.top_level; check_uvars = _40_975.check_uvars; use_eq = false; is_iface = _40_975.is_iface; admit = _40_975.admit; default_effects = _40_975.default_effects})), (_133_742))))

# 612 "FStar.Tc.Env.fst"
let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))

# 614 "FStar.Tc.Env.fst"
let binding_of_binder : FStar_Absyn_Syntax.binder  ->  binding = (fun b -> (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
Binding_typ (((a.FStar_Absyn_Syntax.v), (a.FStar_Absyn_Syntax.sort)))
end
| FStar_Util.Inr (x) -> begin
Binding_var (((x.FStar_Absyn_Syntax.v), (x.FStar_Absyn_Syntax.sort)))
end))

# 618 "FStar.Tc.Env.fst"
let binders : env  ->  FStar_Absyn_Syntax.binders = (fun env -> (FStar_List.fold_left (fun out b -> (match (b) with
| Binding_var (x, t) -> begin
(let _133_760 = (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_133_760)::out)
end
| Binding_typ (a, k) -> begin
(let _133_761 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_133_761)::out)
end
| _40_999 -> begin
out
end)) [] env.gamma))

# 624 "FStar.Tc.Env.fst"
let t_binders : env  ->  FStar_Absyn_Syntax.binders = (fun env -> (FStar_List.fold_left (fun out b -> (match (b) with
| Binding_var (_40_1004) -> begin
out
end
| Binding_typ (a, k) -> begin
(let _133_766 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_133_766)::out)
end
| _40_1011 -> begin
out
end)) [] env.gamma))

# 630 "FStar.Tc.Env.fst"
let idents : env  ->  FStar_Absyn_Syntax.freevars = (fun env -> (let _133_770 = (let _133_769 = (binders env)
in (FStar_All.pipe_right _133_769 (FStar_List.map Prims.fst)))
in (FStar_Absyn_Syntax.freevars_of_list _133_770)))

# 632 "FStar.Tc.Env.fst"
let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (
# 633 "FStar.Tc.Env.fst"
let keys = (FStar_List.fold_left (fun keys _40_13 -> (match (_40_13) with
| Binding_sig (s) -> begin
(let _133_775 = (FStar_Absyn_Util.lids_of_sigelt s)
in (FStar_List.append _133_775 keys))
end
| _40_1019 -> begin
keys
end)) [] env.gamma)
in (let _133_780 = (sigtab env)
in (FStar_Util.smap_fold _133_780 (fun _40_1021 v keys -> (let _133_779 = (FStar_Absyn_Util.lids_of_sigelt v)
in (FStar_List.append _133_779 keys))) keys))))




