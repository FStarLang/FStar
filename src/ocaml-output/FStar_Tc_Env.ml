
type binding =
| Binding_var of (FStar_Absyn_Syntax.bvvdef * FStar_Absyn_Syntax.typ)
| Binding_typ of (FStar_Absyn_Syntax.btvdef * FStar_Absyn_Syntax.knd)
| Binding_lid of (FStar_Absyn_Syntax.lident * FStar_Absyn_Syntax.typ)
| Binding_sig of FStar_Absyn_Syntax.sigelt

let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_typ = (fun _discr_ -> (match (_discr_) with
| Binding_typ (_) -> begin
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

let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_29_16) -> begin
_29_16
end))

let ___Binding_typ____0 = (fun projectee -> (match (projectee) with
| Binding_typ (_29_19) -> begin
_29_19
end))

let ___Binding_lid____0 = (fun projectee -> (match (projectee) with
| Binding_lid (_29_22) -> begin
_29_22
end))

let ___Binding_sig____0 = (fun projectee -> (match (projectee) with
| Binding_sig (_29_25) -> begin
_29_25
end))

type sigtable =
FStar_Absyn_Syntax.sigelt FStar_Util.smap

let default_table_size = 200

let strlid_of_sigelt = (fun se -> (match ((FStar_Absyn_Util.lid_of_sigelt se)) with
| None -> begin
None
end
| Some (l) -> begin
(let _95_59 = (FStar_Absyn_Syntax.text_of_lid l)
in Some (_95_59))
end))

let signature_to_sigtables = (fun s -> (let ht = (FStar_Util.smap_create default_table_size)
in (let _29_35 = (FStar_List.iter (fun se -> (let lids = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (FStar_Util.smap_add ht l.FStar_Absyn_Syntax.str se)) lids))) s)
in ht)))

let modules_to_sigtables = (fun mods -> (let _95_66 = (FStar_List.collect (fun _29_41 -> (match (_29_41) with
| (_29_39, m) -> begin
m.FStar_Absyn_Syntax.declarations
end)) mods)
in (signature_to_sigtables _95_66)))

type level =
| Expr
| Type
| Kind

let is_Expr = (fun _discr_ -> (match (_discr_) with
| Expr -> begin
true
end
| _ -> begin
false
end))

let is_Type = (fun _discr_ -> (match (_discr_) with
| Type -> begin
true
end
| _ -> begin
false
end))

let is_Kind = (fun _discr_ -> (match (_discr_) with
| Kind -> begin
true
end
| _ -> begin
false
end))

type mlift =
FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ

type edge =
{msource : FStar_Absyn_Syntax.lident; mtarget : FStar_Absyn_Syntax.lident; mlift : mlift}

let is_Mkedge = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkedge"))

type effects =
{decls : FStar_Absyn_Syntax.eff_decl Prims.list; order : edge Prims.list; joins : (FStar_Absyn_Syntax.lident * FStar_Absyn_Syntax.lident * FStar_Absyn_Syntax.lident * mlift * mlift) Prims.list}

let is_Mkeffects = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeffects"))

type env =
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Absyn_Syntax.lident; gamma : binding Prims.list; modules : FStar_Absyn_Syntax.modul Prims.list; expected_typ : FStar_Absyn_Syntax.typ Prims.option; level : level; sigtab : sigtable Prims.list; is_pattern : Prims.bool; instantiate_targs : Prims.bool; instantiate_vargs : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; default_effects : (FStar_Absyn_Syntax.lident * FStar_Absyn_Syntax.lident) Prims.list} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Absyn_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit; solve : env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}

let is_Mkenv = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))

let is_Mksolver_t = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksolver_t"))

let bound_vars = (fun env -> (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _29_1 -> (match (_29_1) with
| Binding_typ (a, k) -> begin
(let _95_292 = (FStar_All.pipe_left (fun _95_291 -> FStar_Util.Inl (_95_291)) (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_95_292)::[])
end
| Binding_var (x, t) -> begin
(let _95_294 = (FStar_All.pipe_left (fun _95_293 -> FStar_Util.Inr (_95_293)) (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_95_294)::[])
end
| Binding_lid (_29_95) -> begin
[]
end
| Binding_sig (_29_98) -> begin
[]
end)))))

let has_interface = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Absyn_Syntax.is_interface && (FStar_Absyn_Syntax.lid_equals m.FStar_Absyn_Syntax.name l))))))

let debug = (fun env l -> ((let _95_305 = (FStar_ST.read FStar_Options.debug)
in (FStar_All.pipe_right _95_305 (FStar_Util.for_some (fun x -> (env.curmodule.FStar_Absyn_Syntax.str = x))))) && (FStar_Options.debug_level_geq l)))

let show = (fun env -> (let _95_309 = (FStar_ST.read FStar_Options.show_signatures)
in (FStar_All.pipe_right _95_309 (FStar_Util.for_some (fun x -> (env.curmodule.FStar_Absyn_Syntax.str = x))))))

let new_sigtab = (fun _29_108 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))

let sigtab = (fun env -> (FStar_List.hd env.sigtab))

let push = (fun env msg -> (let _29_112 = (env.solver.push msg)
in (let _29_114 = env
in (let _95_319 = (let _95_318 = (let _95_317 = (sigtab env)
in (FStar_Util.smap_copy _95_317))
in (_95_318)::env.sigtab)
in {solver = _29_114.solver; range = _29_114.range; curmodule = _29_114.curmodule; gamma = _29_114.gamma; modules = _29_114.modules; expected_typ = _29_114.expected_typ; level = _29_114.level; sigtab = _95_319; is_pattern = _29_114.is_pattern; instantiate_targs = _29_114.instantiate_targs; instantiate_vargs = _29_114.instantiate_vargs; effects = _29_114.effects; generalize = _29_114.generalize; letrecs = _29_114.letrecs; top_level = _29_114.top_level; check_uvars = _29_114.check_uvars; use_eq = _29_114.use_eq; is_iface = _29_114.is_iface; admit = _29_114.admit; default_effects = _29_114.default_effects}))))

let mark = (fun env -> (let _29_117 = (env.solver.mark "USER MARK")
in (let _29_119 = env
in (let _95_324 = (let _95_323 = (let _95_322 = (sigtab env)
in (FStar_Util.smap_copy _95_322))
in (_95_323)::env.sigtab)
in {solver = _29_119.solver; range = _29_119.range; curmodule = _29_119.curmodule; gamma = _29_119.gamma; modules = _29_119.modules; expected_typ = _29_119.expected_typ; level = _29_119.level; sigtab = _95_324; is_pattern = _29_119.is_pattern; instantiate_targs = _29_119.instantiate_targs; instantiate_vargs = _29_119.instantiate_vargs; effects = _29_119.effects; generalize = _29_119.generalize; letrecs = _29_119.letrecs; top_level = _29_119.top_level; check_uvars = _29_119.check_uvars; use_eq = _29_119.use_eq; is_iface = _29_119.is_iface; admit = _29_119.admit; default_effects = _29_119.default_effects}))))

let commit_mark = (fun env -> (let _29_122 = (env.solver.commit_mark "USER MARK")
in (let sigtab = (match (env.sigtab) with
| hd::_29_126::tl -> begin
(hd)::tl
end
| _29_131 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _29_133 = env
in {solver = _29_133.solver; range = _29_133.range; curmodule = _29_133.curmodule; gamma = _29_133.gamma; modules = _29_133.modules; expected_typ = _29_133.expected_typ; level = _29_133.level; sigtab = sigtab; is_pattern = _29_133.is_pattern; instantiate_targs = _29_133.instantiate_targs; instantiate_vargs = _29_133.instantiate_vargs; effects = _29_133.effects; generalize = _29_133.generalize; letrecs = _29_133.letrecs; top_level = _29_133.top_level; check_uvars = _29_133.check_uvars; use_eq = _29_133.use_eq; is_iface = _29_133.is_iface; admit = _29_133.admit; default_effects = _29_133.default_effects}))))

let reset_mark = (fun env -> (let _29_136 = (env.solver.reset_mark "USER MARK")
in (let _29_138 = env
in (let _95_329 = (FStar_List.tl env.sigtab)
in {solver = _29_138.solver; range = _29_138.range; curmodule = _29_138.curmodule; gamma = _29_138.gamma; modules = _29_138.modules; expected_typ = _29_138.expected_typ; level = _29_138.level; sigtab = _95_329; is_pattern = _29_138.is_pattern; instantiate_targs = _29_138.instantiate_targs; instantiate_vargs = _29_138.instantiate_vargs; effects = _29_138.effects; generalize = _29_138.generalize; letrecs = _29_138.letrecs; top_level = _29_138.top_level; check_uvars = _29_138.check_uvars; use_eq = _29_138.use_eq; is_iface = _29_138.is_iface; admit = _29_138.admit; default_effects = _29_138.default_effects}))))

let pop = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(FStar_All.failwith "Too many pops")
end
| _29_148::tl -> begin
(let _29_150 = (env.solver.pop msg)
in (let _29_152 = env
in {solver = _29_152.solver; range = _29_152.range; curmodule = _29_152.curmodule; gamma = _29_152.gamma; modules = _29_152.modules; expected_typ = _29_152.expected_typ; level = _29_152.level; sigtab = tl; is_pattern = _29_152.is_pattern; instantiate_targs = _29_152.instantiate_targs; instantiate_vargs = _29_152.instantiate_vargs; effects = _29_152.effects; generalize = _29_152.generalize; letrecs = _29_152.letrecs; top_level = _29_152.top_level; check_uvars = _29_152.check_uvars; use_eq = _29_152.use_eq; is_iface = _29_152.is_iface; admit = _29_152.admit; default_effects = _29_152.default_effects}))
end))

let initial_env = (fun solver module_lid -> (let _95_339 = (let _95_338 = (new_sigtab ())
in (_95_338)::[])
in {solver = solver; range = FStar_Absyn_Syntax.dummyRange; curmodule = module_lid; gamma = []; modules = []; expected_typ = None; level = Expr; sigtab = _95_339; is_pattern = false; instantiate_targs = true; instantiate_vargs = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = true; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []}))

let effect_decl_opt = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Absyn_Syntax.lid_equals d.FStar_Absyn_Syntax.mname l)))))

let name_not_found = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Absyn_Syntax.str))

let variable_not_found = (fun v -> (let _95_348 = (FStar_Absyn_Print.strBvd v)
in (FStar_Util.format1 "Variable \"%s\" not found" _95_348)))

let get_effect_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _95_356 = (let _95_355 = (let _95_354 = (name_not_found l)
in (let _95_353 = (FStar_Absyn_Syntax.range_of_lid l)
in (_95_354, _95_353)))
in FStar_Absyn_Syntax.Error (_95_355))
in (Prims.raise _95_356))
end
| Some (md) -> begin
md
end))

let join = (fun env l1 l2 -> (match ((FStar_Absyn_Syntax.lid_equals l1 l2)) with
| true -> begin
(l1, (fun t wp -> wp), (fun t wp -> wp))
end
| false -> begin
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _29_181 -> (match (_29_181) with
| (m1, m2, _29_176, _29_178, _29_180) -> begin
((FStar_Absyn_Syntax.lid_equals l1 m1) && (FStar_Absyn_Syntax.lid_equals l2 m2))
end))))) with
| None -> begin
(let _95_412 = (let _95_411 = (let _95_410 = (let _95_409 = (FStar_Absyn_Print.sli l1)
in (let _95_408 = (FStar_Absyn_Print.sli l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _95_409 _95_408)))
in (_95_410, env.range))
in FStar_Absyn_Syntax.Error (_95_411))
in (Prims.raise _95_412))
end
| Some (_29_184, _29_186, m3, j1, j2) -> begin
(m3, j1, j2)
end)
end))

let monad_leq = (fun env l1 l2 -> (match ((FStar_Absyn_Syntax.lid_equals l1 l2)) with
| true -> begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end
| false -> begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Absyn_Syntax.lid_equals l1 e.msource) && (FStar_Absyn_Syntax.lid_equals l2 e.mtarget)))))
end))

let wp_sig_aux = (fun decls m -> (match ((FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Absyn_Syntax.lid_equals d.FStar_Absyn_Syntax.mname m))))) with
| None -> begin
(let _95_427 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Absyn_Syntax.str)
in (FStar_All.failwith _95_427))
end
| Some (md) -> begin
(match (md.FStar_Absyn_Syntax.signature.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow ((FStar_Util.Inl (a), _29_217)::(FStar_Util.Inl (wp), _29_212)::(FStar_Util.Inl (wlp), _29_207)::[], {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_effect; FStar_Absyn_Syntax.tk = _29_227; FStar_Absyn_Syntax.pos = _29_225; FStar_Absyn_Syntax.fvs = _29_223; FStar_Absyn_Syntax.uvs = _29_221}) -> begin
(a, wp.FStar_Absyn_Syntax.sort)
end
| _29_233 -> begin
(FStar_All.failwith "Impossible")
end)
end))

let wp_signature = (fun env m -> (wp_sig_aux env.effects.decls m))

let default_effect = (fun env l -> (FStar_Util.find_map env.default_effects (fun _29_240 -> (match (_29_240) with
| (l', m) -> begin
(match ((FStar_Absyn_Syntax.lid_equals l l')) with
| true -> begin
Some (m)
end
| false -> begin
None
end)
end))))

let build_lattice = (fun env se -> (match (se) with
| FStar_Absyn_Syntax.Sig_effect_abbrev (l, _29_245, c, quals, r) -> begin
(match ((FStar_Util.find_map quals (fun _29_2 -> (match (_29_2) with
| FStar_Absyn_Syntax.DefaultEffect (n) -> begin
n
end
| _29_255 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(let _29_259 = env
in {solver = _29_259.solver; range = _29_259.range; curmodule = _29_259.curmodule; gamma = _29_259.gamma; modules = _29_259.modules; expected_typ = _29_259.expected_typ; level = _29_259.level; sigtab = _29_259.sigtab; is_pattern = _29_259.is_pattern; instantiate_targs = _29_259.instantiate_targs; instantiate_vargs = _29_259.instantiate_vargs; effects = _29_259.effects; generalize = _29_259.generalize; letrecs = _29_259.letrecs; top_level = _29_259.top_level; check_uvars = _29_259.check_uvars; use_eq = _29_259.use_eq; is_iface = _29_259.is_iface; admit = _29_259.admit; default_effects = ((e, l))::env.default_effects})
end)
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, _29_263) -> begin
(let effects = (let _29_266 = env.effects
in {decls = (ne)::env.effects.decls; order = _29_266.order; joins = _29_266.joins})
in (let _29_269 = env
in {solver = _29_269.solver; range = _29_269.range; curmodule = _29_269.curmodule; gamma = _29_269.gamma; modules = _29_269.modules; expected_typ = _29_269.expected_typ; level = _29_269.level; sigtab = _29_269.sigtab; is_pattern = _29_269.is_pattern; instantiate_targs = _29_269.instantiate_targs; instantiate_vargs = _29_269.instantiate_vargs; effects = effects; generalize = _29_269.generalize; letrecs = _29_269.letrecs; top_level = _29_269.top_level; check_uvars = _29_269.check_uvars; use_eq = _29_269.use_eq; is_iface = _29_269.is_iface; admit = _29_269.admit; default_effects = _29_269.default_effects}))
end
| FStar_Absyn_Syntax.Sig_sub_effect (sub, _29_273) -> begin
(let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _95_448 = (e1.mlift r wp1)
in (e2.mlift r _95_448)))})
in (let mk_lift = (fun lift_t r wp1 -> (let _95_459 = (let _95_458 = (let _95_457 = (FStar_Absyn_Syntax.targ r)
in (let _95_456 = (let _95_455 = (FStar_Absyn_Syntax.targ wp1)
in (_95_455)::[])
in (_95_457)::_95_456))
in (lift_t, _95_458))
in (FStar_Absyn_Syntax.mk_Typ_app _95_459 None wp1.FStar_Absyn_Syntax.pos)))
in (let edge = {msource = sub.FStar_Absyn_Syntax.source; mtarget = sub.FStar_Absyn_Syntax.target; mlift = (mk_lift sub.FStar_Absyn_Syntax.lift)}
in (let id_edge = (fun l -> {msource = sub.FStar_Absyn_Syntax.source; mtarget = sub.FStar_Absyn_Syntax.target; mlift = (fun t wp -> wp)})
in (let print_mlift = (fun l -> (let arg = (let _95_476 = (FStar_Absyn_Syntax.lid_of_path (("ARG")::[]) FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Util.ftv _95_476 FStar_Absyn_Syntax.mk_Kind_type))
in (let wp = (let _95_477 = (FStar_Absyn_Syntax.lid_of_path (("WP")::[]) FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Util.ftv _95_477 FStar_Absyn_Syntax.mk_Kind_unknown))
in (let _95_478 = (l arg wp)
in (FStar_Absyn_Print.typ_to_string _95_478)))))
in (let order = (edge)::env.effects.order
in (let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Absyn_Syntax.mname)))
in (let find_edge = (fun order _29_301 -> (match (_29_301) with
| (i, j) -> begin
(match ((FStar_Absyn_Syntax.lid_equals i j)) with
| true -> begin
(FStar_All.pipe_right (id_edge i) (fun _95_484 -> Some (_95_484)))
end
| false -> begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Absyn_Syntax.lid_equals e.msource i) && (FStar_Absyn_Syntax.lid_equals e.mtarget j)))))
end)
end))
in (let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _95_492 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (match ((FStar_Absyn_Syntax.lid_equals i k)) with
| true -> begin
[]
end
| false -> begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> (match ((FStar_Absyn_Syntax.lid_equals j k)) with
| true -> begin
[]
end
| false -> begin
(match ((let _95_491 = (find_edge order (i, k))
in (let _95_490 = (find_edge order (k, j))
in (_95_491, _95_490)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _29_313 -> begin
[]
end)
end))))
end))))
in (FStar_List.append order _95_492))) order))
in (let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Absyn_Syntax.lid_equals e1.msource e2.msource) && (FStar_Absyn_Syntax.lid_equals e1.mtarget e2.mtarget))) order)
in (let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _95_500 = (find_edge order (i, k))
in (let _95_499 = (find_edge order (j, k))
in (_95_500, _95_499)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _29_330, _29_332) -> begin
(match (((let _95_501 = (find_edge order (k, ub))
in (FStar_Util.is_some _95_501)) && (not ((let _95_502 = (find_edge order (ub, k))
in (FStar_Util.is_some _95_502)))))) with
| true -> begin
Some ((k, ik, jk))
end
| false -> begin
bopt
end)
end)
end
| _29_336 -> begin
bopt
end)) None))
in (match (join_opt) with
| None -> begin
[]
end
| Some (k, e1, e2) -> begin
((i, j, k, e1.mlift, e2.mlift))::[]
end))))))))
in (let effects = (let _29_345 = env.effects
in {decls = _29_345.decls; order = order; joins = joins})
in (let _29_348 = env
in {solver = _29_348.solver; range = _29_348.range; curmodule = _29_348.curmodule; gamma = _29_348.gamma; modules = _29_348.modules; expected_typ = _29_348.expected_typ; level = _29_348.level; sigtab = _29_348.sigtab; is_pattern = _29_348.is_pattern; instantiate_targs = _29_348.instantiate_targs; instantiate_vargs = _29_348.instantiate_vargs; effects = effects; generalize = _29_348.generalize; letrecs = _29_348.letrecs; top_level = _29_348.top_level; check_uvars = _29_348.check_uvars; use_eq = _29_348.use_eq; is_iface = _29_348.is_iface; admit = _29_348.admit; default_effects = _29_348.default_effects})))))))))))))
end
| _29_351 -> begin
env
end))

let rec add_sigelt = (fun env se -> (match (se) with
| FStar_Absyn_Syntax.Sig_bundle (ses, _29_356, _29_358, _29_360) -> begin
(add_sigelts env ses)
end
| _29_364 -> begin
(let lids = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _95_510 = (sigtab env)
in (FStar_Util.smap_add _95_510 l.FStar_Absyn_Syntax.str se))) lids))
end))
and add_sigelts = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))

let empty_lid = (let _95_514 = (let _95_513 = (FStar_Absyn_Syntax.id_of_text "")
in (_95_513)::[])
in (FStar_Absyn_Syntax.lid_of_ids _95_514))

let finish_module = (fun env m -> (let sigs = (match ((FStar_Absyn_Syntax.lid_equals m.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid)) with
| true -> begin
(FStar_All.pipe_right env.gamma (FStar_List.collect (fun _29_3 -> (match (_29_3) with
| Binding_sig (se) -> begin
(se)::[]
end
| _29_375 -> begin
[]
end))))
end
| false -> begin
m.FStar_Absyn_Syntax.exports
end)
in (let _29_377 = (add_sigelts env sigs)
in (let _29_379 = env
in {solver = _29_379.solver; range = _29_379.range; curmodule = empty_lid; gamma = []; modules = (m)::env.modules; expected_typ = _29_379.expected_typ; level = _29_379.level; sigtab = _29_379.sigtab; is_pattern = _29_379.is_pattern; instantiate_targs = _29_379.instantiate_targs; instantiate_vargs = _29_379.instantiate_vargs; effects = _29_379.effects; generalize = _29_379.generalize; letrecs = _29_379.letrecs; top_level = _29_379.top_level; check_uvars = _29_379.check_uvars; use_eq = _29_379.use_eq; is_iface = _29_379.is_iface; admit = _29_379.admit; default_effects = _29_379.default_effects}))))

let set_level = (fun env level -> (let _29_383 = env
in {solver = _29_383.solver; range = _29_383.range; curmodule = _29_383.curmodule; gamma = _29_383.gamma; modules = _29_383.modules; expected_typ = _29_383.expected_typ; level = level; sigtab = _29_383.sigtab; is_pattern = _29_383.is_pattern; instantiate_targs = _29_383.instantiate_targs; instantiate_vargs = _29_383.instantiate_vargs; effects = _29_383.effects; generalize = _29_383.generalize; letrecs = _29_383.letrecs; top_level = _29_383.top_level; check_uvars = _29_383.check_uvars; use_eq = _29_383.use_eq; is_iface = _29_383.is_iface; admit = _29_383.admit; default_effects = _29_383.default_effects}))

let is_level = (fun env level -> (env.level = level))

let modules = (fun env -> env.modules)

let current_module = (fun env -> env.curmodule)

let set_current_module = (fun env lid -> (let _29_391 = env
in {solver = _29_391.solver; range = _29_391.range; curmodule = lid; gamma = _29_391.gamma; modules = _29_391.modules; expected_typ = _29_391.expected_typ; level = _29_391.level; sigtab = _29_391.sigtab; is_pattern = _29_391.is_pattern; instantiate_targs = _29_391.instantiate_targs; instantiate_vargs = _29_391.instantiate_vargs; effects = _29_391.effects; generalize = _29_391.generalize; letrecs = _29_391.letrecs; top_level = _29_391.top_level; check_uvars = _29_391.check_uvars; use_eq = _29_391.use_eq; is_iface = _29_391.is_iface; admit = _29_391.admit; default_effects = _29_391.default_effects}))

let set_range = (fun e r -> (match ((r = FStar_Absyn_Syntax.dummyRange)) with
| true -> begin
e
end
| false -> begin
(let _29_395 = e
in {solver = _29_395.solver; range = r; curmodule = _29_395.curmodule; gamma = _29_395.gamma; modules = _29_395.modules; expected_typ = _29_395.expected_typ; level = _29_395.level; sigtab = _29_395.sigtab; is_pattern = _29_395.is_pattern; instantiate_targs = _29_395.instantiate_targs; instantiate_vargs = _29_395.instantiate_vargs; effects = _29_395.effects; generalize = _29_395.generalize; letrecs = _29_395.letrecs; top_level = _29_395.top_level; check_uvars = _29_395.check_uvars; use_eq = _29_395.use_eq; is_iface = _29_395.is_iface; admit = _29_395.admit; default_effects = _29_395.default_effects})
end))

let get_range = (fun e -> e.range)

let find_in_sigtab = (fun env lid -> (let _95_547 = (sigtab env)
in (let _95_546 = (FStar_Absyn_Syntax.text_of_lid lid)
in (FStar_Util.smap_try_find _95_547 _95_546))))

let lookup_bvvdef = (fun env bvvd -> (FStar_Util.find_map env.gamma (fun _29_4 -> (match (_29_4) with
| Binding_var (id, t) when (FStar_Absyn_Util.bvd_eq id bvvd) -> begin
Some (t)
end
| _29_408 -> begin
None
end))))

let lookup_bvar = (fun env bv -> (match ((lookup_bvvdef env bv.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _95_559 = (let _95_558 = (let _95_557 = (variable_not_found bv.FStar_Absyn_Syntax.v)
in (_95_557, (FStar_Absyn_Util.range_of_bvd bv.FStar_Absyn_Syntax.v)))
in FStar_Absyn_Syntax.Error (_95_558))
in (Prims.raise _95_559))
end
| Some (t) -> begin
t
end))

let lookup_qname = (fun env lid -> (let in_cur_mod = (fun l -> (let cur = (current_module env)
in (match ((l.FStar_Absyn_Syntax.nsstr = cur.FStar_Absyn_Syntax.str)) with
| true -> begin
true
end
| false -> begin
(match ((FStar_Util.starts_with l.FStar_Absyn_Syntax.nsstr cur.FStar_Absyn_Syntax.str)) with
| true -> begin
(let lns = (FStar_List.append l.FStar_Absyn_Syntax.ns ((l.FStar_Absyn_Syntax.ident)::[]))
in (let cur = (FStar_List.append cur.FStar_Absyn_Syntax.ns ((cur.FStar_Absyn_Syntax.ident)::[]))
in (let rec aux = (fun c l -> (match ((c, l)) with
| ([], _29_426) -> begin
true
end
| (_29_429, []) -> begin
false
end
| (hd::tl, hd'::tl') when (hd.FStar_Absyn_Syntax.idText = hd'.FStar_Absyn_Syntax.idText) -> begin
(aux tl tl')
end
| _29_440 -> begin
false
end))
in (aux cur lns))))
end
| false -> begin
false
end)
end)))
in (let cur_mod = (in_cur_mod lid)
in (let found = (match (cur_mod) with
| true -> begin
(FStar_Util.find_map env.gamma (fun _29_5 -> (match (_29_5) with
| Binding_lid (l, t) -> begin
(match ((FStar_Absyn_Syntax.lid_equals lid l)) with
| true -> begin
Some (FStar_Util.Inl (t))
end
| false -> begin
None
end)
end
| Binding_sig (FStar_Absyn_Syntax.Sig_bundle (ses, _29_449, _29_451, _29_453)) -> begin
(FStar_Util.find_map ses (fun se -> (match ((let _95_572 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _95_572 (FStar_Util.for_some (FStar_Absyn_Syntax.lid_equals lid))))) with
| true -> begin
Some (FStar_Util.Inr (se))
end
| false -> begin
None
end)))
end
| Binding_sig (s) -> begin
(let lids = (FStar_Absyn_Util.lids_of_sigelt s)
in (match ((FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Absyn_Syntax.lid_equals lid)))) with
| true -> begin
Some (FStar_Util.Inr (s))
end
| false -> begin
None
end))
end
| _29_462 -> begin
None
end)))
end
| false -> begin
None
end)
in (match ((FStar_Util.is_some found)) with
| true -> begin
found
end
| false -> begin
(match (((not (cur_mod)) || (has_interface env env.curmodule))) with
| true -> begin
(match ((find_in_sigtab env lid)) with
| Some (se) -> begin
Some (FStar_Util.Inr (se))
end
| None -> begin
None
end)
end
| false -> begin
None
end)
end)))))

let lookup_datacon = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_29_470, t, _29_473, _29_475, _29_477, _29_479))) -> begin
t
end
| _29_485 -> begin
(let _95_580 = (let _95_579 = (let _95_578 = (name_not_found lid)
in (let _95_577 = (FStar_Absyn_Syntax.range_of_lid lid)
in (_95_578, _95_577)))
in FStar_Absyn_Syntax.Error (_95_579))
in (Prims.raise _95_580))
end))

let lookup_kind_abbrev = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_kind_abbrev (l, binders, k, _29_492))) -> begin
(l, binders, k)
end
| _29_498 -> begin
(let _95_588 = (let _95_587 = (let _95_586 = (name_not_found lid)
in (let _95_585 = (FStar_Absyn_Syntax.range_of_lid lid)
in (_95_586, _95_585)))
in FStar_Absyn_Syntax.Error (_95_587))
in (Prims.raise _95_588))
end))

let lookup_projector = (fun env lid i -> (let fail = (fun _29_503 -> (match (()) with
| () -> begin
(let _95_599 = (let _95_598 = (FStar_Util.string_of_int i)
in (let _95_597 = (FStar_Absyn_Print.sli lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _95_598 _95_597)))
in (FStar_All.failwith _95_599))
end))
in (let t = (lookup_datacon env lid)
in (match ((let _95_600 = (FStar_Absyn_Util.compress_typ t)
in _95_600.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, _29_507) -> begin
(match (((i < 0) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| false -> begin
(let b = (FStar_List.nth binders i)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _95_601 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (FStar_All.pipe_right _95_601 Prims.fst))
end
| FStar_Util.Inr (x) -> begin
(let _95_602 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (FStar_All.pipe_right _95_602 Prims.fst))
end))
end)
end
| _29_516 -> begin
(fail ())
end))))

let try_lookup_val_decl = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_29_520, t, q, _29_524))) -> begin
Some ((t, q))
end
| _29_530 -> begin
None
end))

let lookup_val_decl = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_29_534, t, _29_537, _29_539))) -> begin
t
end
| _29_545 -> begin
(let _95_614 = (let _95_613 = (let _95_612 = (name_not_found lid)
in (let _95_611 = (FStar_Absyn_Syntax.range_of_lid lid)
in (_95_612, _95_611)))
in FStar_Absyn_Syntax.Error (_95_613))
in (Prims.raise _95_614))
end))

let lookup_lid = (fun env lid -> (let not_found = (fun _29_549 -> (match (()) with
| () -> begin
(let _95_624 = (let _95_623 = (let _95_622 = (name_not_found lid)
in (let _95_621 = (FStar_Absyn_Syntax.range_of_lid lid)
in (_95_622, _95_621)))
in FStar_Absyn_Syntax.Error (_95_623))
in (Prims.raise _95_624))
end))
in (let mapper = (fun _29_6 -> (match (_29_6) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_, t, _, _, _, _))) | (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_, t, _, _))) | (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_let ((_, {FStar_Absyn_Syntax.lbname = _; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _; FStar_Absyn_Syntax.lbdef = _}::[]), _, _, _))) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_let ((_29_596, lbs), _29_600, _29_602, _29_604)) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (_29_610) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (lid') -> begin
(match ((FStar_Absyn_Syntax.lid_equals lid lid')) with
| true -> begin
Some (lb.FStar_Absyn_Syntax.lbtyp)
end
| false -> begin
None
end)
end)))
end
| t -> begin
None
end))
in (match ((let _95_628 = (lookup_qname env lid)
in (FStar_Util.bind_opt _95_628 mapper))) with
| Some (t) -> begin
(let _29_618 = t
in (let _95_629 = (FStar_Absyn_Syntax.range_of_lid lid)
in {FStar_Absyn_Syntax.n = _29_618.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _29_618.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = _95_629; FStar_Absyn_Syntax.fvs = _29_618.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _29_618.FStar_Absyn_Syntax.uvs}))
end
| None -> begin
(not_found ())
end))))

let is_datacon = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_29_624, _29_626, quals, _29_629))) -> begin
(FStar_All.pipe_right quals (FStar_Util.for_some (fun _29_7 -> (match (_29_7) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _29_637 -> begin
false
end))))
end
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_29_639, t, _29_642, _29_644, _29_646, _29_648))) -> begin
true
end
| _29_654 -> begin
false
end))

let is_record = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_29_658, _29_660, _29_662, _29_664, _29_666, tags, _29_669))) -> begin
(FStar_Util.for_some (fun _29_8 -> (match (_29_8) with
| (FStar_Absyn_Syntax.RecordType (_)) | (FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _29_682 -> begin
false
end)) tags)
end
| _29_684 -> begin
false
end))

let lookup_datacons_of_typ = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_29_688, _29_690, _29_692, _29_694, datas, _29_697, _29_699))) -> begin
(let _95_646 = (FStar_List.map (fun l -> (let _95_645 = (lookup_lid env l)
in (l, _95_645))) datas)
in Some (_95_646))
end
| _29_706 -> begin
None
end))

let lookup_effect_abbrev = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, binders, c, quals, _29_714))) -> begin
(match ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _29_9 -> (match (_29_9) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _29_722 -> begin
false
end))))) with
| true -> begin
None
end
| false -> begin
Some ((binders, c))
end)
end
| _29_724 -> begin
None
end))

let lookup_typ_abbrev = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _29_730, t, quals, _29_734))) -> begin
(match ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _29_10 -> (match (_29_10) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _29_742 -> begin
false
end))))) with
| true -> begin
None
end
| false -> begin
(let t = (FStar_Absyn_Util.close_with_lam tps t)
in (let _95_657 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named ((t, lid))))
in Some (_95_657)))
end)
end
| _29_745 -> begin
None
end))

let lookup_btvdef = (fun env btvd -> (FStar_Util.find_map env.gamma (fun _29_11 -> (match (_29_11) with
| Binding_typ (id, k) when (FStar_Absyn_Util.bvd_eq id btvd) -> begin
Some (k)
end
| _29_754 -> begin
None
end))))

let lookup_btvar = (fun env btv -> (match ((lookup_btvdef env btv.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _95_669 = (let _95_668 = (let _95_667 = (variable_not_found btv.FStar_Absyn_Syntax.v)
in (_95_667, (FStar_Absyn_Util.range_of_bvd btv.FStar_Absyn_Syntax.v)))
in FStar_Absyn_Syntax.Error (_95_668))
in (Prims.raise _95_669))
end
| Some (k) -> begin
k
end))

let lookup_typ_lid = (fun env ftv -> (match ((lookup_qname env ftv)) with
| (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _, _, _, _)))) | (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, _, _, _)))) -> begin
(FStar_Absyn_Util.close_kind tps k)
end
| _29_788 -> begin
(let _95_677 = (let _95_676 = (let _95_675 = (name_not_found ftv)
in (let _95_674 = (FStar_Absyn_Syntax.range_of_lid ftv)
in (_95_675, _95_674)))
in FStar_Absyn_Syntax.Error (_95_676))
in (Prims.raise _95_677))
end))

let is_projector = (fun env l -> (match ((lookup_qname env l)) with
| (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_, _, _, _, _, quals, _)))) | (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_, _, quals, _)))) -> begin
(FStar_Util.for_some (fun _29_12 -> (match (_29_12) with
| FStar_Absyn_Syntax.Projector (_29_820) -> begin
true
end
| _29_823 -> begin
false
end)) quals)
end
| _29_825 -> begin
false
end))

let try_lookup_effect_lid = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_new_effect (ne, _29_830))) -> begin
(let _95_688 = (FStar_Absyn_Util.close_kind ne.FStar_Absyn_Syntax.binders ne.FStar_Absyn_Syntax.signature)
in (FStar_All.pipe_right _95_688 (fun _95_687 -> Some (_95_687))))
end
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, binders, _29_838, _29_840, _29_842))) -> begin
(let _95_690 = (FStar_Absyn_Util.close_kind binders FStar_Absyn_Syntax.mk_Kind_effect)
in (FStar_All.pipe_right _95_690 (fun _95_689 -> Some (_95_689))))
end
| _29_848 -> begin
None
end))

let lookup_effect_lid = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _95_698 = (let _95_697 = (let _95_696 = (name_not_found ftv)
in (let _95_695 = (FStar_Absyn_Syntax.range_of_lid ftv)
in (_95_696, _95_695)))
in FStar_Absyn_Syntax.Error (_95_697))
in (Prims.raise _95_698))
end
| Some (k) -> begin
k
end))

let lookup_operator = (fun env opname -> (let primName = (FStar_Absyn_Syntax.lid_of_path (("Prims")::((Prims.strcat "_dummy_" opname.FStar_Absyn_Syntax.idText))::[]) FStar_Absyn_Syntax.dummyRange)
in (lookup_lid env primName)))

let push_sigelt = (fun env s -> (build_lattice (let _29_859 = env
in {solver = _29_859.solver; range = _29_859.range; curmodule = _29_859.curmodule; gamma = (Binding_sig (s))::env.gamma; modules = _29_859.modules; expected_typ = _29_859.expected_typ; level = _29_859.level; sigtab = _29_859.sigtab; is_pattern = _29_859.is_pattern; instantiate_targs = _29_859.instantiate_targs; instantiate_vargs = _29_859.instantiate_vargs; effects = _29_859.effects; generalize = _29_859.generalize; letrecs = _29_859.letrecs; top_level = _29_859.top_level; check_uvars = _29_859.check_uvars; use_eq = _29_859.use_eq; is_iface = _29_859.is_iface; admit = _29_859.admit; default_effects = _29_859.default_effects}) s))

let push_local_binding = (fun env b -> (let _29_863 = env
in {solver = _29_863.solver; range = _29_863.range; curmodule = _29_863.curmodule; gamma = (b)::env.gamma; modules = _29_863.modules; expected_typ = _29_863.expected_typ; level = _29_863.level; sigtab = _29_863.sigtab; is_pattern = _29_863.is_pattern; instantiate_targs = _29_863.instantiate_targs; instantiate_vargs = _29_863.instantiate_vargs; effects = _29_863.effects; generalize = _29_863.generalize; letrecs = _29_863.letrecs; top_level = _29_863.top_level; check_uvars = _29_863.check_uvars; use_eq = _29_863.use_eq; is_iface = _29_863.is_iface; admit = _29_863.admit; default_effects = _29_863.default_effects}))

let uvars_in_env = (fun env -> (let no_uvs = (let _95_715 = (FStar_Absyn_Syntax.new_uv_set ())
in (let _95_714 = (FStar_Absyn_Syntax.new_uvt_set ())
in (let _95_713 = (FStar_Absyn_Syntax.new_uvt_set ())
in {FStar_Absyn_Syntax.uvars_k = _95_715; FStar_Absyn_Syntax.uvars_t = _95_714; FStar_Absyn_Syntax.uvars_e = _95_713})))
in (let ext = (fun out uvs -> (let _29_870 = out
in (let _95_722 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_k uvs.FStar_Absyn_Syntax.uvars_k)
in (let _95_721 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_t uvs.FStar_Absyn_Syntax.uvars_t)
in (let _95_720 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_e uvs.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _95_722; FStar_Absyn_Syntax.uvars_t = _95_721; FStar_Absyn_Syntax.uvars_e = _95_720})))))
in (let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_lid (_, t)::tl) | (Binding_var (_, t)::tl) -> begin
(let _95_728 = (let _95_727 = (FStar_Absyn_Util.uvars_in_typ t)
in (ext out _95_727))
in (aux _95_728 tl))
end
| Binding_typ (_29_890, k)::tl -> begin
(let _95_730 = (let _95_729 = (FStar_Absyn_Util.uvars_in_kind k)
in (ext out _95_729))
in (aux _95_730 tl))
end
| Binding_sig (_29_898)::_29_896 -> begin
out
end))
in (aux no_uvs env.gamma)))))

let push_module = (fun env m -> (let _29_903 = (add_sigelts env m.FStar_Absyn_Syntax.exports)
in (let _29_905 = env
in {solver = _29_905.solver; range = _29_905.range; curmodule = _29_905.curmodule; gamma = []; modules = (m)::env.modules; expected_typ = None; level = _29_905.level; sigtab = _29_905.sigtab; is_pattern = _29_905.is_pattern; instantiate_targs = _29_905.instantiate_targs; instantiate_vargs = _29_905.instantiate_vargs; effects = _29_905.effects; generalize = _29_905.generalize; letrecs = _29_905.letrecs; top_level = _29_905.top_level; check_uvars = _29_905.check_uvars; use_eq = _29_905.use_eq; is_iface = _29_905.is_iface; admit = _29_905.admit; default_effects = _29_905.default_effects})))

let set_expected_typ = (fun env t -> (let _29_909 = env
in {solver = _29_909.solver; range = _29_909.range; curmodule = _29_909.curmodule; gamma = _29_909.gamma; modules = _29_909.modules; expected_typ = Some (t); level = _29_909.level; sigtab = _29_909.sigtab; is_pattern = _29_909.is_pattern; instantiate_targs = _29_909.instantiate_targs; instantiate_vargs = _29_909.instantiate_vargs; effects = _29_909.effects; generalize = _29_909.generalize; letrecs = _29_909.letrecs; top_level = _29_909.top_level; check_uvars = _29_909.check_uvars; use_eq = false; is_iface = _29_909.is_iface; admit = _29_909.admit; default_effects = _29_909.default_effects}))

let expected_typ = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

let clear_expected_typ = (fun env -> (let _95_743 = (expected_typ env)
in ((let _29_916 = env
in {solver = _29_916.solver; range = _29_916.range; curmodule = _29_916.curmodule; gamma = _29_916.gamma; modules = _29_916.modules; expected_typ = None; level = _29_916.level; sigtab = _29_916.sigtab; is_pattern = _29_916.is_pattern; instantiate_targs = _29_916.instantiate_targs; instantiate_vargs = _29_916.instantiate_vargs; effects = _29_916.effects; generalize = _29_916.generalize; letrecs = _29_916.letrecs; top_level = _29_916.top_level; check_uvars = _29_916.check_uvars; use_eq = false; is_iface = _29_916.is_iface; admit = _29_916.admit; default_effects = _29_916.default_effects}), _95_743)))

let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))

let binding_of_binder = (fun b -> (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
Binding_typ ((a.FStar_Absyn_Syntax.v, a.FStar_Absyn_Syntax.sort))
end
| FStar_Util.Inr (x) -> begin
Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))
end))

let binders = (fun env -> (FStar_List.fold_left (fun out b -> (match (b) with
| Binding_var (x, t) -> begin
(let _95_761 = (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_95_761)::out)
end
| Binding_typ (a, k) -> begin
(let _95_762 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_95_762)::out)
end
| _29_940 -> begin
out
end)) [] env.gamma))

let t_binders = (fun env -> (FStar_List.fold_left (fun out b -> (match (b) with
| Binding_var (_29_945) -> begin
out
end
| Binding_typ (a, k) -> begin
(let _95_767 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_95_767)::out)
end
| _29_952 -> begin
out
end)) [] env.gamma))

let idents = (fun env -> (let _95_771 = (let _95_770 = (binders env)
in (FStar_All.pipe_right _95_770 (FStar_List.map Prims.fst)))
in (FStar_Absyn_Syntax.freevars_of_list _95_771)))

let lidents = (fun env -> (let keys = (FStar_List.fold_left (fun keys _29_13 -> (match (_29_13) with
| Binding_sig (s) -> begin
(let _95_776 = (FStar_Absyn_Util.lids_of_sigelt s)
in (FStar_List.append _95_776 keys))
end
| _29_960 -> begin
keys
end)) [] env.gamma)
in (let _95_781 = (sigtab env)
in (FStar_Util.smap_fold _95_781 (fun _29_962 v keys -> (let _95_780 = (FStar_Absyn_Util.lids_of_sigelt v)
in (FStar_List.append _95_780 keys))) keys))))




