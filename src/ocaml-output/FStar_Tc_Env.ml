
open Prims
type binding =
| Binding_var of (FStar_Absyn_Syntax.bvvdef * FStar_Absyn_Syntax.typ)
| Binding_typ of (FStar_Absyn_Syntax.btvdef * FStar_Absyn_Syntax.knd)
| Binding_lid of (FStar_Ident.lident * FStar_Absyn_Syntax.typ)
| Binding_sig of FStar_Absyn_Syntax.sigelt

let is_Binding_var : binding  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_typ : binding  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Binding_typ (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_lid : binding  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Binding_lid (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_sig : binding  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Binding_sig (_) -> begin
true
end
| _ -> begin
false
end))

let ___Binding_var____0 : binding  ->  (FStar_Absyn_Syntax.bvvdef * FStar_Absyn_Syntax.typ) = (fun projectee -> (match (projectee) with
| Binding_var (_45_16) -> begin
_45_16
end))

let ___Binding_typ____0 : binding  ->  (FStar_Absyn_Syntax.btvdef * FStar_Absyn_Syntax.knd) = (fun projectee -> (match (projectee) with
| Binding_typ (_45_19) -> begin
_45_19
end))

let ___Binding_lid____0 : binding  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.typ) = (fun projectee -> (match (projectee) with
| Binding_lid (_45_22) -> begin
_45_22
end))

let ___Binding_sig____0 : binding  ->  FStar_Absyn_Syntax.sigelt = (fun projectee -> (match (projectee) with
| Binding_sig (_45_25) -> begin
_45_25
end))

type sigtable =
FStar_Absyn_Syntax.sigelt FStar_Util.smap

let default_table_size : Prims.int = 200

let strlid_of_sigelt : FStar_Absyn_Syntax.sigelt  ->  Prims.string Prims.option = (fun se -> (match ((FStar_Absyn_Util.lid_of_sigelt se)) with
| None -> begin
None
end
| Some (l) -> begin
Some ((FStar_Ident.text_of_lid l))
end))

let signature_to_sigtables : FStar_Absyn_Syntax.sigelt Prims.list  ->  FStar_Absyn_Syntax.sigelt FStar_Util.smap = (fun s -> (let ht = (FStar_Util.smap_create default_table_size)
in (let _45_35 = (FStar_List.iter (fun se -> (let lids = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (FStar_Util.smap_add ht l.FStar_Ident.str se)) lids))) s)
in ht)))

let modules_to_sigtables = (fun mods -> (let _148_65 = (FStar_List.collect (fun _45_41 -> (match (_45_41) with
| (_45_39, m) -> begin
m.FStar_Absyn_Syntax.declarations
end)) mods)
in (signature_to_sigtables _148_65)))

type level =
| Expr
| Type
| Kind

let is_Expr : level  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Expr -> begin
true
end
| _ -> begin
false
end))

let is_Type : level  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Type -> begin
true
end
| _ -> begin
false
end))

let is_Kind : level  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Kind -> begin
true
end
| _ -> begin
false
end))

type mlift =
FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ

type edge =
{msource : FStar_Ident.lident; mtarget : FStar_Ident.lident; mlift : mlift}

let is_Mkedge : edge  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkedge"))))

type effects =
{decls : FStar_Absyn_Syntax.eff_decl Prims.list; order : edge Prims.list; joins : (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list}

let is_Mkeffects : effects  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeffects"))))

type env =
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; modules : FStar_Absyn_Syntax.modul Prims.list; expected_typ : FStar_Absyn_Syntax.typ Prims.option; level : level; sigtab : sigtable Prims.list; is_pattern : Prims.bool; instantiate_targs : Prims.bool; instantiate_vargs : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; default_effects : (FStar_Ident.lident * FStar_Ident.lident) Prims.list} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Absyn_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit; solve : env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}

let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

let is_Mksolver_t : solver_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksolver_t"))))

let bound_vars : env  ->  (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either Prims.list = (fun env -> (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _45_1 -> (match (_45_1) with
| Binding_typ (a, k) -> begin
(let _148_291 = (FStar_All.pipe_left (fun _148_290 -> FStar_Util.Inl (_148_290)) (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_148_291)::[])
end
| Binding_var (x, t) -> begin
(let _148_293 = (FStar_All.pipe_left (fun _148_292 -> FStar_Util.Inr (_148_292)) (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_148_293)::[])
end
| Binding_lid (_45_95) -> begin
[]
end
| Binding_sig (_45_98) -> begin
[]
end)))))

let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Absyn_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Absyn_Syntax.name l))))))

let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> ((let _148_304 = (FStar_ST.read FStar_Options.debug)
in (FStar_All.pipe_right _148_304 (FStar_Util.for_some (fun x -> (env.curmodule.FStar_Ident.str = x))))) && (FStar_Options.debug_level_geq l)))

let show : env  ->  Prims.bool = (fun env -> (let _148_308 = (FStar_ST.read FStar_Options.show_signatures)
in (FStar_All.pipe_right _148_308 (FStar_Util.for_some (fun x -> (env.curmodule.FStar_Ident.str = x))))))

let new_sigtab = (fun _45_108 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))

let sigtab : env  ->  sigtable = (fun env -> (FStar_List.hd env.sigtab))

let push : env  ->  Prims.string  ->  env = (fun env msg -> (let _45_112 = (env.solver.push msg)
in (let _45_114 = env
in (let _148_318 = (let _148_317 = (let _148_316 = (sigtab env)
in (FStar_Util.smap_copy _148_316))
in (_148_317)::env.sigtab)
in {solver = _45_114.solver; range = _45_114.range; curmodule = _45_114.curmodule; gamma = _45_114.gamma; modules = _45_114.modules; expected_typ = _45_114.expected_typ; level = _45_114.level; sigtab = _148_318; is_pattern = _45_114.is_pattern; instantiate_targs = _45_114.instantiate_targs; instantiate_vargs = _45_114.instantiate_vargs; effects = _45_114.effects; generalize = _45_114.generalize; letrecs = _45_114.letrecs; top_level = _45_114.top_level; check_uvars = _45_114.check_uvars; use_eq = _45_114.use_eq; is_iface = _45_114.is_iface; admit = _45_114.admit; default_effects = _45_114.default_effects}))))

let mark : env  ->  env = (fun env -> (let _45_117 = (env.solver.mark "USER MARK")
in (let _45_119 = env
in (let _148_323 = (let _148_322 = (let _148_321 = (sigtab env)
in (FStar_Util.smap_copy _148_321))
in (_148_322)::env.sigtab)
in {solver = _45_119.solver; range = _45_119.range; curmodule = _45_119.curmodule; gamma = _45_119.gamma; modules = _45_119.modules; expected_typ = _45_119.expected_typ; level = _45_119.level; sigtab = _148_323; is_pattern = _45_119.is_pattern; instantiate_targs = _45_119.instantiate_targs; instantiate_vargs = _45_119.instantiate_vargs; effects = _45_119.effects; generalize = _45_119.generalize; letrecs = _45_119.letrecs; top_level = _45_119.top_level; check_uvars = _45_119.check_uvars; use_eq = _45_119.use_eq; is_iface = _45_119.is_iface; admit = _45_119.admit; default_effects = _45_119.default_effects}))))

let commit_mark : env  ->  env = (fun env -> (let _45_122 = (env.solver.commit_mark "USER MARK")
in (let sigtab = (match (env.sigtab) with
| hd::_45_126::tl -> begin
(hd)::tl
end
| _45_131 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _45_133 = env
in {solver = _45_133.solver; range = _45_133.range; curmodule = _45_133.curmodule; gamma = _45_133.gamma; modules = _45_133.modules; expected_typ = _45_133.expected_typ; level = _45_133.level; sigtab = sigtab; is_pattern = _45_133.is_pattern; instantiate_targs = _45_133.instantiate_targs; instantiate_vargs = _45_133.instantiate_vargs; effects = _45_133.effects; generalize = _45_133.generalize; letrecs = _45_133.letrecs; top_level = _45_133.top_level; check_uvars = _45_133.check_uvars; use_eq = _45_133.use_eq; is_iface = _45_133.is_iface; admit = _45_133.admit; default_effects = _45_133.default_effects}))))

let reset_mark : env  ->  env = (fun env -> (let _45_136 = (env.solver.reset_mark "USER MARK")
in (let _45_138 = env
in (let _148_328 = (FStar_List.tl env.sigtab)
in {solver = _45_138.solver; range = _45_138.range; curmodule = _45_138.curmodule; gamma = _45_138.gamma; modules = _45_138.modules; expected_typ = _45_138.expected_typ; level = _45_138.level; sigtab = _148_328; is_pattern = _45_138.is_pattern; instantiate_targs = _45_138.instantiate_targs; instantiate_vargs = _45_138.instantiate_vargs; effects = _45_138.effects; generalize = _45_138.generalize; letrecs = _45_138.letrecs; top_level = _45_138.top_level; check_uvars = _45_138.check_uvars; use_eq = _45_138.use_eq; is_iface = _45_138.is_iface; admit = _45_138.admit; default_effects = _45_138.default_effects}))))

let pop : env  ->  Prims.string  ->  env = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(FStar_All.failwith "Too many pops")
end
| _45_148::tl -> begin
(let _45_150 = (env.solver.pop msg)
in (let _45_152 = env
in {solver = _45_152.solver; range = _45_152.range; curmodule = _45_152.curmodule; gamma = _45_152.gamma; modules = _45_152.modules; expected_typ = _45_152.expected_typ; level = _45_152.level; sigtab = tl; is_pattern = _45_152.is_pattern; instantiate_targs = _45_152.instantiate_targs; instantiate_vargs = _45_152.instantiate_vargs; effects = _45_152.effects; generalize = _45_152.generalize; letrecs = _45_152.letrecs; top_level = _45_152.top_level; check_uvars = _45_152.check_uvars; use_eq = _45_152.use_eq; is_iface = _45_152.is_iface; admit = _45_152.admit; default_effects = _45_152.default_effects}))
end))

let initial_env : solver_t  ->  FStar_Absyn_Syntax.lident  ->  env = (fun solver module_lid -> (let _148_338 = (let _148_337 = (new_sigtab ())
in (_148_337)::[])
in {solver = solver; range = FStar_Absyn_Syntax.dummyRange; curmodule = module_lid; gamma = []; modules = []; expected_typ = None; level = Expr; sigtab = _148_338; is_pattern = false; instantiate_targs = true; instantiate_vargs = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = true; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []}))

let effect_decl_opt : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Absyn_Syntax.mname l)))))

let name_not_found : FStar_Absyn_Syntax.lident  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))

let variable_not_found = (fun v -> (let _148_347 = (FStar_Absyn_Print.strBvd v)
in (FStar_Util.format1 "Variable \"%s\" not found" _148_347)))

let get_effect_decl : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _148_354 = (let _148_353 = (let _148_352 = (name_not_found l)
in (_148_352, (FStar_Ident.range_of_lid l)))
in FStar_Absyn_Syntax.Error (_148_353))
in (Prims.raise _148_354))
end
| Some (md) -> begin
md
end))

let join : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.lident  ->  (FStar_Absyn_Syntax.lident * mlift * mlift) = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
(l1, (fun t wp -> wp), (fun t wp -> wp))
end else begin
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _45_181 -> (match (_45_181) with
| (m1, m2, _45_176, _45_178, _45_180) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _148_410 = (let _148_409 = (let _148_408 = (let _148_407 = (FStar_Absyn_Print.sli l1)
in (let _148_406 = (FStar_Absyn_Print.sli l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _148_407 _148_406)))
in (_148_408, env.range))
in FStar_Absyn_Syntax.Error (_148_409))
in (Prims.raise _148_410))
end
| Some (_45_184, _45_186, m3, j1, j2) -> begin
(m3, j1, j2)
end)
end)

let monad_leq : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.lident  ->  edge Prims.option = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end else begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end)

let wp_sig_aux : FStar_Absyn_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) = (fun decls m -> (match ((FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Absyn_Syntax.mname m))))) with
| None -> begin
(let _148_425 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _148_425))
end
| Some (md) -> begin
(match (md.FStar_Absyn_Syntax.signature.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow ((FStar_Util.Inl (a), _45_217)::(FStar_Util.Inl (wp), _45_212)::(FStar_Util.Inl (wlp), _45_207)::[], {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_effect; FStar_Absyn_Syntax.tk = _45_227; FStar_Absyn_Syntax.pos = _45_225; FStar_Absyn_Syntax.fvs = _45_223; FStar_Absyn_Syntax.uvs = _45_221}) -> begin
(a, wp.FStar_Absyn_Syntax.sort)
end
| _45_233 -> begin
(FStar_All.failwith "Impossible")
end)
end))

let wp_signature : env  ->  FStar_Absyn_Syntax.lident  ->  (FStar_Absyn_Syntax.btvar * FStar_Absyn_Syntax.knd) = (fun env m -> (wp_sig_aux env.effects.decls m))

let default_effect : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.lident Prims.option = (fun env l -> (FStar_Util.find_map env.default_effects (fun _45_240 -> (match (_45_240) with
| (l', m) -> begin
if (FStar_Ident.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))

let build_lattice : env  ->  FStar_Absyn_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Absyn_Syntax.Sig_effect_abbrev (l, _45_245, c, quals, r) -> begin
(match ((FStar_Util.find_map quals (fun _45_2 -> (match (_45_2) with
| FStar_Absyn_Syntax.DefaultEffect (n) -> begin
n
end
| _45_255 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(let _45_259 = env
in {solver = _45_259.solver; range = _45_259.range; curmodule = _45_259.curmodule; gamma = _45_259.gamma; modules = _45_259.modules; expected_typ = _45_259.expected_typ; level = _45_259.level; sigtab = _45_259.sigtab; is_pattern = _45_259.is_pattern; instantiate_targs = _45_259.instantiate_targs; instantiate_vargs = _45_259.instantiate_vargs; effects = _45_259.effects; generalize = _45_259.generalize; letrecs = _45_259.letrecs; top_level = _45_259.top_level; check_uvars = _45_259.check_uvars; use_eq = _45_259.use_eq; is_iface = _45_259.is_iface; admit = _45_259.admit; default_effects = ((e, l))::env.default_effects})
end)
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, _45_263) -> begin
(let effects = (let _45_266 = env.effects
in {decls = (ne)::env.effects.decls; order = _45_266.order; joins = _45_266.joins})
in (let _45_269 = env
in {solver = _45_269.solver; range = _45_269.range; curmodule = _45_269.curmodule; gamma = _45_269.gamma; modules = _45_269.modules; expected_typ = _45_269.expected_typ; level = _45_269.level; sigtab = _45_269.sigtab; is_pattern = _45_269.is_pattern; instantiate_targs = _45_269.instantiate_targs; instantiate_vargs = _45_269.instantiate_vargs; effects = effects; generalize = _45_269.generalize; letrecs = _45_269.letrecs; top_level = _45_269.top_level; check_uvars = _45_269.check_uvars; use_eq = _45_269.use_eq; is_iface = _45_269.is_iface; admit = _45_269.admit; default_effects = _45_269.default_effects}))
end
| FStar_Absyn_Syntax.Sig_sub_effect (sub, _45_273) -> begin
(let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _148_446 = (e1.mlift r wp1)
in (e2.mlift r _148_446)))})
in (let mk_lift = (fun lift_t r wp1 -> (FStar_Absyn_Syntax.mk_Typ_app (lift_t, ((FStar_Absyn_Syntax.targ r))::((FStar_Absyn_Syntax.targ wp1))::[]) None wp1.FStar_Absyn_Syntax.pos))
in (let edge = {msource = sub.FStar_Absyn_Syntax.source; mtarget = sub.FStar_Absyn_Syntax.target; mlift = (mk_lift sub.FStar_Absyn_Syntax.lift)}
in (let id_edge = (fun l -> {msource = sub.FStar_Absyn_Syntax.source; mtarget = sub.FStar_Absyn_Syntax.target; mlift = (fun t wp -> wp)})
in (let print_mlift = (fun l -> (let arg = (let _148_469 = (FStar_Absyn_Syntax.lid_of_path (("ARG")::[]) FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Util.ftv _148_469 FStar_Absyn_Syntax.mk_Kind_type))
in (let wp = (let _148_470 = (FStar_Absyn_Syntax.lid_of_path (("WP")::[]) FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Util.ftv _148_470 FStar_Absyn_Syntax.mk_Kind_unknown))
in (let _148_471 = (l arg wp)
in (FStar_Absyn_Print.typ_to_string _148_471)))))
in (let order = (edge)::env.effects.order
in (let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Absyn_Syntax.mname)))
in (let find_edge = (fun order _45_301 -> (match (_45_301) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _148_477 -> Some (_148_477)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _148_485 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _148_484 = (find_edge order (i, k))
in (let _148_483 = (find_edge order (k, j))
in (_148_484, _148_483)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _45_313 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _148_485))) order))
in (let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _148_493 = (find_edge order (i, k))
in (let _148_492 = (find_edge order (j, k))
in (_148_493, _148_492)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _45_330, _45_332) -> begin
if ((let _148_494 = (find_edge order (k, ub))
in (FStar_Util.is_some _148_494)) && (not ((let _148_495 = (find_edge order (ub, k))
in (FStar_Util.is_some _148_495))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _45_336 -> begin
bopt
end)) None))
in (match (join_opt) with
| None -> begin
[]
end
| Some (k, e1, e2) -> begin
((i, j, k, e1.mlift, e2.mlift))::[]
end))))))))
in (let effects = (let _45_345 = env.effects
in {decls = _45_345.decls; order = order; joins = joins})
in (let _45_348 = env
in {solver = _45_348.solver; range = _45_348.range; curmodule = _45_348.curmodule; gamma = _45_348.gamma; modules = _45_348.modules; expected_typ = _45_348.expected_typ; level = _45_348.level; sigtab = _45_348.sigtab; is_pattern = _45_348.is_pattern; instantiate_targs = _45_348.instantiate_targs; instantiate_vargs = _45_348.instantiate_vargs; effects = effects; generalize = _45_348.generalize; letrecs = _45_348.letrecs; top_level = _45_348.top_level; check_uvars = _45_348.check_uvars; use_eq = _45_348.use_eq; is_iface = _45_348.is_iface; admit = _45_348.admit; default_effects = _45_348.default_effects})))))))))))))
end
| _45_351 -> begin
env
end))

let rec add_sigelt : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Absyn_Syntax.Sig_bundle (ses, _45_356, _45_358, _45_360) -> begin
(add_sigelts env ses)
end
| _45_364 -> begin
(let lids = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _148_503 = (sigtab env)
in (FStar_Util.smap_add _148_503 l.FStar_Ident.str se))) lids))
end))
and add_sigelts : env  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))

let empty_lid : FStar_Ident.lident = (FStar_Absyn_Syntax.lid_of_ids (((FStar_Absyn_Syntax.id_of_text ""))::[]))

let finish_module : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env m -> (let sigs = if (FStar_Ident.lid_equals m.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid) then begin
(FStar_All.pipe_right env.gamma (FStar_List.collect (fun _45_3 -> (match (_45_3) with
| Binding_sig (se) -> begin
(se)::[]
end
| _45_375 -> begin
[]
end))))
end else begin
m.FStar_Absyn_Syntax.exports
end
in (let _45_377 = (add_sigelts env sigs)
in (let _45_379 = env
in {solver = _45_379.solver; range = _45_379.range; curmodule = empty_lid; gamma = []; modules = (m)::env.modules; expected_typ = _45_379.expected_typ; level = _45_379.level; sigtab = _45_379.sigtab; is_pattern = _45_379.is_pattern; instantiate_targs = _45_379.instantiate_targs; instantiate_vargs = _45_379.instantiate_vargs; effects = _45_379.effects; generalize = _45_379.generalize; letrecs = _45_379.letrecs; top_level = _45_379.top_level; check_uvars = _45_379.check_uvars; use_eq = _45_379.use_eq; is_iface = _45_379.is_iface; admit = _45_379.admit; default_effects = _45_379.default_effects}))))

let set_level : env  ->  level  ->  env = (fun env level -> (let _45_383 = env
in {solver = _45_383.solver; range = _45_383.range; curmodule = _45_383.curmodule; gamma = _45_383.gamma; modules = _45_383.modules; expected_typ = _45_383.expected_typ; level = level; sigtab = _45_383.sigtab; is_pattern = _45_383.is_pattern; instantiate_targs = _45_383.instantiate_targs; instantiate_vargs = _45_383.instantiate_vargs; effects = _45_383.effects; generalize = _45_383.generalize; letrecs = _45_383.letrecs; top_level = _45_383.top_level; check_uvars = _45_383.check_uvars; use_eq = _45_383.use_eq; is_iface = _45_383.is_iface; admit = _45_383.admit; default_effects = _45_383.default_effects}))

let is_level : env  ->  level  ->  Prims.bool = (fun env level -> (env.level = level))

let modules : env  ->  FStar_Absyn_Syntax.modul Prims.list = (fun env -> env.modules)

let current_module : env  ->  FStar_Absyn_Syntax.lident = (fun env -> env.curmodule)

let set_current_module : env  ->  FStar_Absyn_Syntax.lident  ->  env = (fun env lid -> (let _45_391 = env
in {solver = _45_391.solver; range = _45_391.range; curmodule = lid; gamma = _45_391.gamma; modules = _45_391.modules; expected_typ = _45_391.expected_typ; level = _45_391.level; sigtab = _45_391.sigtab; is_pattern = _45_391.is_pattern; instantiate_targs = _45_391.instantiate_targs; instantiate_vargs = _45_391.instantiate_vargs; effects = _45_391.effects; generalize = _45_391.generalize; letrecs = _45_391.letrecs; top_level = _45_391.top_level; check_uvars = _45_391.check_uvars; use_eq = _45_391.use_eq; is_iface = _45_391.is_iface; admit = _45_391.admit; default_effects = _45_391.default_effects}))

let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Absyn_Syntax.dummyRange) then begin
e
end else begin
(let _45_395 = e
in {solver = _45_395.solver; range = r; curmodule = _45_395.curmodule; gamma = _45_395.gamma; modules = _45_395.modules; expected_typ = _45_395.expected_typ; level = _45_395.level; sigtab = _45_395.sigtab; is_pattern = _45_395.is_pattern; instantiate_targs = _45_395.instantiate_targs; instantiate_vargs = _45_395.instantiate_vargs; effects = _45_395.effects; generalize = _45_395.generalize; letrecs = _45_395.letrecs; top_level = _45_395.top_level; check_uvars = _45_395.check_uvars; use_eq = _45_395.use_eq; is_iface = _45_395.is_iface; admit = _45_395.admit; default_effects = _45_395.default_effects})
end)

let get_range : env  ->  FStar_Range.range = (fun e -> e.range)

let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.sigelt Prims.option = (fun env lid -> (let _148_537 = (sigtab env)
in (FStar_Util.smap_try_find _148_537 (FStar_Ident.text_of_lid lid))))

let lookup_bvvdef : env  ->  FStar_Absyn_Syntax.bvvdef  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env bvvd -> (FStar_Util.find_map env.gamma (fun _45_4 -> (match (_45_4) with
| Binding_var (id, t) when (FStar_Absyn_Util.bvd_eq id bvvd) -> begin
Some (t)
end
| _45_408 -> begin
None
end))))

let lookup_bvar : env  ->  FStar_Absyn_Syntax.bvvar  ->  FStar_Absyn_Syntax.typ = (fun env bv -> (match ((lookup_bvvdef env bv.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _148_549 = (let _148_548 = (let _148_547 = (variable_not_found bv.FStar_Absyn_Syntax.v)
in (_148_547, (FStar_Absyn_Util.range_of_bvd bv.FStar_Absyn_Syntax.v)))
in FStar_Absyn_Syntax.Error (_148_548))
in (Prims.raise _148_549))
end
| Some (t) -> begin
t
end))

let in_cur_mod : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (let cur = (current_module env)
in if (l.FStar_Ident.nsstr = cur.FStar_Ident.str) then begin
true
end else begin
if (FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str) then begin
(let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (let rec aux = (fun c l -> (match ((c, l)) with
| ([], _45_424) -> begin
true
end
| (_45_427, []) -> begin
false
end
| (hd::tl, hd'::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _45_438 -> begin
false
end))
in (aux cur lns))))
end else begin
false
end
end))

let lookup_qname : env  ->  FStar_Absyn_Syntax.lident  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.sigelt) FStar_Util.either Prims.option = (fun env lid -> (let cur_mod = (in_cur_mod env lid)
in (let found = if cur_mod then begin
(FStar_Util.find_map env.gamma (fun _45_5 -> (match (_45_5) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
Some (FStar_Util.Inl (t))
end else begin
None
end
end
| Binding_sig (FStar_Absyn_Syntax.Sig_bundle (ses, _45_449, _45_451, _45_453)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _148_564 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _148_564 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
Some (FStar_Util.Inr (se))
end else begin
None
end))
end
| Binding_sig (s) -> begin
(let lids = (FStar_Absyn_Util.lids_of_sigelt s)
in if (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals lid))) then begin
Some (FStar_Util.Inr (s))
end else begin
None
end)
end
| _45_462 -> begin
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

let lookup_datacon : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.typ = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_45_470, t, (_45_473, tps, _45_476), _45_479, _45_481, _45_483))) -> begin
(let _148_570 = (FStar_List.map (fun _45_491 -> (match (_45_491) with
| (x, _45_490) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit))
end)) tps)
in (FStar_Absyn_Util.close_typ _148_570 t))
end
| _45_493 -> begin
(let _148_573 = (let _148_572 = (let _148_571 = (name_not_found lid)
in (_148_571, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_148_572))
in (Prims.raise _148_573))
end))

let lookup_kind_abbrev : env  ->  FStar_Absyn_Syntax.lident  ->  (FStar_Absyn_Syntax.lident * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_kind_abbrev (l, binders, k, _45_500))) -> begin
(l, binders, k)
end
| _45_506 -> begin
(let _148_580 = (let _148_579 = (let _148_578 = (name_not_found lid)
in (_148_578, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_148_579))
in (Prims.raise _148_580))
end))

let lookup_projector : env  ->  FStar_Absyn_Syntax.lident  ->  Prims.int  ->  FStar_Absyn_Syntax.lident = (fun env lid i -> (let fail = (fun _45_511 -> (match (()) with
| () -> begin
(let _148_591 = (let _148_590 = (FStar_Util.string_of_int i)
in (let _148_589 = (FStar_Absyn_Print.sli lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _148_590 _148_589)))
in (FStar_All.failwith _148_591))
end))
in (let t = (lookup_datacon env lid)
in (match ((let _148_592 = (FStar_Absyn_Util.compress_typ t)
in _148_592.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, _45_515) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(let b = (FStar_List.nth binders i)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _148_593 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (FStar_All.pipe_right _148_593 Prims.fst))
end
| FStar_Util.Inr (x) -> begin
(let _148_594 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (FStar_All.pipe_right _148_594 Prims.fst))
end))
end
end
| _45_524 -> begin
(fail ())
end))))

let try_lookup_val_decl : env  ->  FStar_Absyn_Syntax.lident  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_45_528, t, q, _45_532))) -> begin
Some ((t, q))
end
| _45_538 -> begin
None
end))

let lookup_val_decl : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.typ = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_45_542, t, _45_545, _45_547))) -> begin
t
end
| _45_553 -> begin
(let _148_605 = (let _148_604 = (let _148_603 = (name_not_found lid)
in (_148_603, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_148_604))
in (Prims.raise _148_605))
end))

let lookup_lid : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.typ = (fun env lid -> (let not_found = (fun _45_557 -> (match (()) with
| () -> begin
(let _148_614 = (let _148_613 = (let _148_612 = (name_not_found lid)
in (_148_612, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_148_613))
in (Prims.raise _148_614))
end))
in (let mapper = (fun _45_6 -> (match (_45_6) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_45_560, t, (_45_563, tps, _45_566), _45_569, _45_571, _45_573)) -> begin
(let _148_619 = (let _148_618 = (FStar_List.map (fun _45_580 -> (match (_45_580) with
| (x, _45_579) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit))
end)) tps)
in (FStar_Absyn_Util.close_typ _148_618 t))
in Some (_148_619))
end
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (l, t, qs, _45_587)) -> begin
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
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_let ((_45_592, {FStar_Absyn_Syntax.lbname = _45_599; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _45_596; FStar_Absyn_Syntax.lbdef = _45_594}::[]), _45_604, _45_606, _45_608)) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_let ((_45_613, lbs), _45_617, _45_619, _45_621)) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (_45_627) -> begin
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
in (match ((let _148_621 = (lookup_qname env lid)
in (FStar_Util.bind_opt _148_621 mapper))) with
| Some (t) -> begin
(let _45_635 = t
in {FStar_Absyn_Syntax.n = _45_635.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _45_635.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = (FStar_Absyn_Syntax.range_of_lid lid); FStar_Absyn_Syntax.fvs = _45_635.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _45_635.FStar_Absyn_Syntax.uvs})
end
| None -> begin
(not_found ())
end))))

let is_datacon : env  ->  FStar_Absyn_Syntax.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_45_641, _45_643, quals, _45_646))) -> begin
(FStar_All.pipe_right quals (FStar_Util.for_some (fun _45_7 -> (match (_45_7) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _45_654 -> begin
false
end))))
end
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_45_656, t, _45_659, _45_661, _45_663, _45_665))) -> begin
true
end
| _45_671 -> begin
false
end))

let is_record : env  ->  FStar_Absyn_Syntax.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_45_675, _45_677, _45_679, _45_681, _45_683, tags, _45_686))) -> begin
(FStar_Util.for_some (fun _45_8 -> (match (_45_8) with
| (FStar_Absyn_Syntax.RecordType (_)) | (FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _45_699 -> begin
false
end)) tags)
end
| _45_701 -> begin
false
end))

let lookup_datacons_of_typ : env  ->  FStar_Absyn_Syntax.lident  ->  (FStar_Absyn_Syntax.lident * FStar_Absyn_Syntax.typ) Prims.list Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_45_705, _45_707, _45_709, _45_711, datas, _45_714, _45_716))) -> begin
(let _148_638 = (FStar_List.map (fun l -> (let _148_637 = (lookup_lid env l)
in (l, _148_637))) datas)
in Some (_148_638))
end
| _45_723 -> begin
None
end))

let lookup_effect_abbrev : env  ->  FStar_Absyn_Syntax.lident  ->  (FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.comp) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, binders, c, quals, _45_731))) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _45_9 -> (match (_45_9) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _45_739 -> begin
false
end)))) then begin
None
end else begin
Some ((binders, c))
end
end
| _45_741 -> begin
None
end))

let lookup_typ_abbrev : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _45_747, t, quals, _45_751))) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _45_10 -> (match (_45_10) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _45_759 -> begin
false
end)))) then begin
None
end else begin
(let t = (FStar_Absyn_Util.close_with_lam tps t)
in (let _148_649 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named ((t, lid))))
in Some (_148_649)))
end
end
| _45_762 -> begin
None
end))

let lookup_opaque_typ_abbrev : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _45_768, t, quals, _45_772))) -> begin
(let t = (FStar_Absyn_Util.close_with_lam tps t)
in (let _148_654 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named ((t, lid))))
in Some (_148_654)))
end
| _45_779 -> begin
None
end))

let lookup_btvdef : env  ->  FStar_Absyn_Syntax.btvdef  ->  FStar_Absyn_Syntax.knd Prims.option = (fun env btvd -> (FStar_Util.find_map env.gamma (fun _45_11 -> (match (_45_11) with
| Binding_typ (id, k) when (FStar_Absyn_Util.bvd_eq id btvd) -> begin
Some (k)
end
| _45_788 -> begin
None
end))))

let lookup_btvar : env  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Absyn_Syntax.knd = (fun env btv -> (match ((lookup_btvdef env btv.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _148_666 = (let _148_665 = (let _148_664 = (variable_not_found btv.FStar_Absyn_Syntax.v)
in (_148_664, (FStar_Absyn_Util.range_of_bvd btv.FStar_Absyn_Syntax.v)))
in FStar_Absyn_Syntax.Error (_148_665))
in (Prims.raise _148_666))
end
| Some (k) -> begin
k
end))

let lookup_typ_lid : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.knd = (fun env ftv -> (match ((lookup_qname env ftv)) with
| (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _, _, _, _)))) | (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, _, _, _)))) -> begin
(FStar_Absyn_Util.close_kind tps k)
end
| _45_822 -> begin
(let _148_673 = (let _148_672 = (let _148_671 = (name_not_found ftv)
in (_148_671, (FStar_Ident.range_of_lid ftv)))
in FStar_Absyn_Syntax.Error (_148_672))
in (Prims.raise _148_673))
end))

let is_projector : env  ->  FStar_Absyn_Syntax.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_, _, _, _, _, quals, _)))) | (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_, _, quals, _)))) -> begin
(FStar_Util.for_some (fun _45_12 -> (match (_45_12) with
| FStar_Absyn_Syntax.Projector (_45_854) -> begin
true
end
| _45_857 -> begin
false
end)) quals)
end
| _45_859 -> begin
false
end))

let try_lookup_effect_lid : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.knd Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_new_effect (ne, _45_864))) -> begin
(let _148_684 = (FStar_Absyn_Util.close_kind ne.FStar_Absyn_Syntax.binders ne.FStar_Absyn_Syntax.signature)
in (FStar_All.pipe_right _148_684 (fun _148_683 -> Some (_148_683))))
end
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, binders, _45_872, _45_874, _45_876))) -> begin
(let _148_686 = (FStar_Absyn_Util.close_kind binders FStar_Absyn_Syntax.mk_Kind_effect)
in (FStar_All.pipe_right _148_686 (fun _148_685 -> Some (_148_685))))
end
| _45_882 -> begin
None
end))

let lookup_effect_lid : env  ->  FStar_Absyn_Syntax.lident  ->  FStar_Absyn_Syntax.knd = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _148_693 = (let _148_692 = (let _148_691 = (name_not_found ftv)
in (_148_691, (FStar_Ident.range_of_lid ftv)))
in FStar_Absyn_Syntax.Error (_148_692))
in (Prims.raise _148_693))
end
| Some (k) -> begin
k
end))

let lookup_operator : env  ->  FStar_Absyn_Syntax.ident  ->  FStar_Absyn_Syntax.typ = (fun env opname -> (let primName = (FStar_Ident.lid_of_path (("Prims")::((Prims.strcat "_dummy_" opname.FStar_Ident.idText))::[]) FStar_Absyn_Syntax.dummyRange)
in (lookup_lid env primName)))

let push_sigelt : env  ->  FStar_Absyn_Syntax.sigelt  ->  env = (fun env s -> (build_lattice (let _45_893 = env
in {solver = _45_893.solver; range = _45_893.range; curmodule = _45_893.curmodule; gamma = (Binding_sig (s))::env.gamma; modules = _45_893.modules; expected_typ = _45_893.expected_typ; level = _45_893.level; sigtab = _45_893.sigtab; is_pattern = _45_893.is_pattern; instantiate_targs = _45_893.instantiate_targs; instantiate_vargs = _45_893.instantiate_vargs; effects = _45_893.effects; generalize = _45_893.generalize; letrecs = _45_893.letrecs; top_level = _45_893.top_level; check_uvars = _45_893.check_uvars; use_eq = _45_893.use_eq; is_iface = _45_893.is_iface; admit = _45_893.admit; default_effects = _45_893.default_effects}) s))

let push_local_binding : env  ->  binding  ->  env = (fun env b -> (let _45_897 = env
in {solver = _45_897.solver; range = _45_897.range; curmodule = _45_897.curmodule; gamma = (b)::env.gamma; modules = _45_897.modules; expected_typ = _45_897.expected_typ; level = _45_897.level; sigtab = _45_897.sigtab; is_pattern = _45_897.is_pattern; instantiate_targs = _45_897.instantiate_targs; instantiate_vargs = _45_897.instantiate_vargs; effects = _45_897.effects; generalize = _45_897.generalize; letrecs = _45_897.letrecs; top_level = _45_897.top_level; check_uvars = _45_897.check_uvars; use_eq = _45_897.use_eq; is_iface = _45_897.is_iface; admit = _45_897.admit; default_effects = _45_897.default_effects}))

let uvars_in_env : env  ->  FStar_Absyn_Syntax.uvars = (fun env -> (let no_uvs = (let _148_710 = (FStar_Absyn_Syntax.new_uv_set ())
in (let _148_709 = (FStar_Absyn_Syntax.new_uvt_set ())
in (let _148_708 = (FStar_Absyn_Syntax.new_uvt_set ())
in {FStar_Absyn_Syntax.uvars_k = _148_710; FStar_Absyn_Syntax.uvars_t = _148_709; FStar_Absyn_Syntax.uvars_e = _148_708})))
in (let ext = (fun out uvs -> (let _45_904 = out
in (let _148_717 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_k uvs.FStar_Absyn_Syntax.uvars_k)
in (let _148_716 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_t uvs.FStar_Absyn_Syntax.uvars_t)
in (let _148_715 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_e uvs.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _148_717; FStar_Absyn_Syntax.uvars_t = _148_716; FStar_Absyn_Syntax.uvars_e = _148_715})))))
in (let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_lid (_, t)::tl) | (Binding_var (_, t)::tl) -> begin
(let _148_723 = (let _148_722 = (FStar_Absyn_Util.uvars_in_typ t)
in (ext out _148_722))
in (aux _148_723 tl))
end
| Binding_typ (_45_924, k)::tl -> begin
(let _148_725 = (let _148_724 = (FStar_Absyn_Util.uvars_in_kind k)
in (ext out _148_724))
in (aux _148_725 tl))
end
| Binding_sig (_45_932)::_45_930 -> begin
out
end))
in (aux no_uvs env.gamma)))))

let push_module : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env m -> (let _45_937 = (add_sigelts env m.FStar_Absyn_Syntax.exports)
in (let _45_939 = env
in {solver = _45_939.solver; range = _45_939.range; curmodule = _45_939.curmodule; gamma = []; modules = (m)::env.modules; expected_typ = None; level = _45_939.level; sigtab = _45_939.sigtab; is_pattern = _45_939.is_pattern; instantiate_targs = _45_939.instantiate_targs; instantiate_vargs = _45_939.instantiate_vargs; effects = _45_939.effects; generalize = _45_939.generalize; letrecs = _45_939.letrecs; top_level = _45_939.top_level; check_uvars = _45_939.check_uvars; use_eq = _45_939.use_eq; is_iface = _45_939.is_iface; admit = _45_939.admit; default_effects = _45_939.default_effects})))

let set_expected_typ : env  ->  FStar_Absyn_Syntax.typ  ->  env = (fun env t -> (match (t) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const ({FStar_Absyn_Syntax.v = _45_964; FStar_Absyn_Syntax.sort = {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _45_960; FStar_Absyn_Syntax.pos = _45_958; FStar_Absyn_Syntax.fvs = _45_956; FStar_Absyn_Syntax.uvs = _45_954}; FStar_Absyn_Syntax.p = _45_952}); FStar_Absyn_Syntax.tk = _45_950; FStar_Absyn_Syntax.pos = _45_948; FStar_Absyn_Syntax.fvs = _45_946; FStar_Absyn_Syntax.uvs = _45_944} -> begin
(let _148_735 = (let _148_734 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "Setting expected type to %s with kind unknown" _148_734))
in (FStar_All.failwith _148_735))
end
| _45_969 -> begin
(let _45_970 = env
in {solver = _45_970.solver; range = _45_970.range; curmodule = _45_970.curmodule; gamma = _45_970.gamma; modules = _45_970.modules; expected_typ = Some (t); level = _45_970.level; sigtab = _45_970.sigtab; is_pattern = _45_970.is_pattern; instantiate_targs = _45_970.instantiate_targs; instantiate_vargs = _45_970.instantiate_vargs; effects = _45_970.effects; generalize = _45_970.generalize; letrecs = _45_970.letrecs; top_level = _45_970.top_level; check_uvars = _45_970.check_uvars; use_eq = false; is_iface = _45_970.is_iface; admit = _45_970.admit; default_effects = _45_970.default_effects})
end))

let expected_typ : env  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

let clear_expected_typ : env  ->  (env * FStar_Absyn_Syntax.typ Prims.option) = (fun env -> (let _148_740 = (expected_typ env)
in ((let _45_977 = env
in {solver = _45_977.solver; range = _45_977.range; curmodule = _45_977.curmodule; gamma = _45_977.gamma; modules = _45_977.modules; expected_typ = None; level = _45_977.level; sigtab = _45_977.sigtab; is_pattern = _45_977.is_pattern; instantiate_targs = _45_977.instantiate_targs; instantiate_vargs = _45_977.instantiate_vargs; effects = _45_977.effects; generalize = _45_977.generalize; letrecs = _45_977.letrecs; top_level = _45_977.top_level; check_uvars = _45_977.check_uvars; use_eq = false; is_iface = _45_977.is_iface; admit = _45_977.admit; default_effects = _45_977.default_effects}), _148_740)))

let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))

let binding_of_binder : FStar_Absyn_Syntax.binder  ->  binding = (fun b -> (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
Binding_typ ((a.FStar_Absyn_Syntax.v, a.FStar_Absyn_Syntax.sort))
end
| FStar_Util.Inr (x) -> begin
Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))
end))

let binders : env  ->  FStar_Absyn_Syntax.binders = (fun env -> (FStar_List.fold_left (fun out b -> (match (b) with
| Binding_var (x, t) -> begin
(let _148_758 = (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_148_758)::out)
end
| Binding_typ (a, k) -> begin
(let _148_759 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_148_759)::out)
end
| _45_1001 -> begin
out
end)) [] env.gamma))

let t_binders : env  ->  FStar_Absyn_Syntax.binders = (fun env -> (FStar_List.fold_left (fun out b -> (match (b) with
| Binding_var (_45_1006) -> begin
out
end
| Binding_typ (a, k) -> begin
(let _148_764 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_148_764)::out)
end
| _45_1013 -> begin
out
end)) [] env.gamma))

let idents : env  ->  FStar_Absyn_Syntax.freevars = (fun env -> (let _148_768 = (let _148_767 = (binders env)
in (FStar_All.pipe_right _148_767 (FStar_List.map Prims.fst)))
in (FStar_Absyn_Syntax.freevars_of_list _148_768)))

let lidents : env  ->  FStar_Absyn_Syntax.lident Prims.list = (fun env -> (let keys = (FStar_List.fold_left (fun keys _45_13 -> (match (_45_13) with
| Binding_sig (s) -> begin
(let _148_773 = (FStar_Absyn_Util.lids_of_sigelt s)
in (FStar_List.append _148_773 keys))
end
| _45_1021 -> begin
keys
end)) [] env.gamma)
in (let _148_778 = (sigtab env)
in (FStar_Util.smap_fold _148_778 (fun _45_1023 v keys -> (let _148_777 = (FStar_Absyn_Util.lids_of_sigelt v)
in (FStar_List.append _148_777 keys))) keys))))




