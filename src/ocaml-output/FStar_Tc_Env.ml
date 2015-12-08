
open Prims
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
| Binding_var (_30_16) -> begin
_30_16
end))

let ___Binding_typ____0 = (fun projectee -> (match (projectee) with
| Binding_typ (_30_19) -> begin
_30_19
end))

let ___Binding_lid____0 = (fun projectee -> (match (projectee) with
| Binding_lid (_30_22) -> begin
_30_22
end))

let ___Binding_sig____0 = (fun projectee -> (match (projectee) with
| Binding_sig (_30_25) -> begin
_30_25
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
in (let _30_35 = (FStar_List.iter (fun se -> (let lids = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (FStar_Util.smap_add ht l.FStar_Absyn_Syntax.str se)) lids))) s)
in ht)))

let modules_to_sigtables = (fun mods -> (let _95_66 = (FStar_List.collect (fun _30_41 -> (match (_30_41) with
| (_30_39, m) -> begin
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

let is_Mkedge = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkedge")))

type effects =
{decls : FStar_Absyn_Syntax.eff_decl Prims.list; order : edge Prims.list; joins : (FStar_Absyn_Syntax.lident * FStar_Absyn_Syntax.lident * FStar_Absyn_Syntax.lident * mlift * mlift) Prims.list}

let is_Mkeffects = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeffects")))

type env =
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Absyn_Syntax.lident; gamma : binding Prims.list; modules : FStar_Absyn_Syntax.modul Prims.list; expected_typ : FStar_Absyn_Syntax.typ Prims.option; level : level; sigtab : sigtable Prims.list; is_pattern : Prims.bool; instantiate_targs : Prims.bool; instantiate_vargs : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; default_effects : (FStar_Absyn_Syntax.lident * FStar_Absyn_Syntax.lident) Prims.list} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Absyn_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit; solve : env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}

let is_Mkenv = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv")))

let is_Mksolver_t = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksolver_t")))

let bound_vars = (fun env -> (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _30_1 -> (match (_30_1) with
| Binding_typ (a, k) -> begin
(let _95_292 = (FStar_All.pipe_left (fun _95_291 -> FStar_Util.Inl (_95_291)) (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_95_292)::[])
end
| Binding_var (x, t) -> begin
(let _95_294 = (FStar_All.pipe_left (fun _95_293 -> FStar_Util.Inr (_95_293)) (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_95_294)::[])
end
| Binding_lid (_30_95) -> begin
[]
end
| Binding_sig (_30_98) -> begin
[]
end)))))

let has_interface = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Absyn_Syntax.is_interface && (FStar_Absyn_Syntax.lid_equals m.FStar_Absyn_Syntax.name l))))))

let debug = (fun env l -> ((let _95_305 = (FStar_ST.read FStar_Options.debug)
in (FStar_All.pipe_right _95_305 (FStar_Util.for_some (fun x -> (env.curmodule.FStar_Absyn_Syntax.str = x))))) && (FStar_Options.debug_level_geq l)))

let show = (fun env -> (let _95_309 = (FStar_ST.read FStar_Options.show_signatures)
in (FStar_All.pipe_right _95_309 (FStar_Util.for_some (fun x -> (env.curmodule.FStar_Absyn_Syntax.str = x))))))

let new_sigtab = (fun _30_108 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))

let sigtab = (fun env -> (FStar_List.hd env.sigtab))

let push = (fun env msg -> (let _30_112 = (env.solver.push msg)
in (let _30_114 = env
in (let _95_319 = (let _95_318 = (let _95_317 = (sigtab env)
in (FStar_Util.smap_copy _95_317))
in (_95_318)::env.sigtab)
in {solver = _30_114.solver; range = _30_114.range; curmodule = _30_114.curmodule; gamma = _30_114.gamma; modules = _30_114.modules; expected_typ = _30_114.expected_typ; level = _30_114.level; sigtab = _95_319; is_pattern = _30_114.is_pattern; instantiate_targs = _30_114.instantiate_targs; instantiate_vargs = _30_114.instantiate_vargs; effects = _30_114.effects; generalize = _30_114.generalize; letrecs = _30_114.letrecs; top_level = _30_114.top_level; check_uvars = _30_114.check_uvars; use_eq = _30_114.use_eq; is_iface = _30_114.is_iface; admit = _30_114.admit; default_effects = _30_114.default_effects}))))

let mark = (fun env -> (let _30_117 = (env.solver.mark "USER MARK")
in (let _30_119 = env
in (let _95_324 = (let _95_323 = (let _95_322 = (sigtab env)
in (FStar_Util.smap_copy _95_322))
in (_95_323)::env.sigtab)
in {solver = _30_119.solver; range = _30_119.range; curmodule = _30_119.curmodule; gamma = _30_119.gamma; modules = _30_119.modules; expected_typ = _30_119.expected_typ; level = _30_119.level; sigtab = _95_324; is_pattern = _30_119.is_pattern; instantiate_targs = _30_119.instantiate_targs; instantiate_vargs = _30_119.instantiate_vargs; effects = _30_119.effects; generalize = _30_119.generalize; letrecs = _30_119.letrecs; top_level = _30_119.top_level; check_uvars = _30_119.check_uvars; use_eq = _30_119.use_eq; is_iface = _30_119.is_iface; admit = _30_119.admit; default_effects = _30_119.default_effects}))))

let commit_mark = (fun env -> (let _30_122 = (env.solver.commit_mark "USER MARK")
in (let sigtab = (match (env.sigtab) with
| hd::_30_126::tl -> begin
(hd)::tl
end
| _30_131 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _30_133 = env
in {solver = _30_133.solver; range = _30_133.range; curmodule = _30_133.curmodule; gamma = _30_133.gamma; modules = _30_133.modules; expected_typ = _30_133.expected_typ; level = _30_133.level; sigtab = sigtab; is_pattern = _30_133.is_pattern; instantiate_targs = _30_133.instantiate_targs; instantiate_vargs = _30_133.instantiate_vargs; effects = _30_133.effects; generalize = _30_133.generalize; letrecs = _30_133.letrecs; top_level = _30_133.top_level; check_uvars = _30_133.check_uvars; use_eq = _30_133.use_eq; is_iface = _30_133.is_iface; admit = _30_133.admit; default_effects = _30_133.default_effects}))))

let reset_mark = (fun env -> (let _30_136 = (env.solver.reset_mark "USER MARK")
in (let _30_138 = env
in (let _95_329 = (FStar_List.tl env.sigtab)
in {solver = _30_138.solver; range = _30_138.range; curmodule = _30_138.curmodule; gamma = _30_138.gamma; modules = _30_138.modules; expected_typ = _30_138.expected_typ; level = _30_138.level; sigtab = _95_329; is_pattern = _30_138.is_pattern; instantiate_targs = _30_138.instantiate_targs; instantiate_vargs = _30_138.instantiate_vargs; effects = _30_138.effects; generalize = _30_138.generalize; letrecs = _30_138.letrecs; top_level = _30_138.top_level; check_uvars = _30_138.check_uvars; use_eq = _30_138.use_eq; is_iface = _30_138.is_iface; admit = _30_138.admit; default_effects = _30_138.default_effects}))))

let pop = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(FStar_All.failwith "Too many pops")
end
| _30_148::tl -> begin
(let _30_150 = (env.solver.pop msg)
in (let _30_152 = env
in {solver = _30_152.solver; range = _30_152.range; curmodule = _30_152.curmodule; gamma = _30_152.gamma; modules = _30_152.modules; expected_typ = _30_152.expected_typ; level = _30_152.level; sigtab = tl; is_pattern = _30_152.is_pattern; instantiate_targs = _30_152.instantiate_targs; instantiate_vargs = _30_152.instantiate_vargs; effects = _30_152.effects; generalize = _30_152.generalize; letrecs = _30_152.letrecs; top_level = _30_152.top_level; check_uvars = _30_152.check_uvars; use_eq = _30_152.use_eq; is_iface = _30_152.is_iface; admit = _30_152.admit; default_effects = _30_152.default_effects}))
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

let join = (fun env l1 l2 -> if (FStar_Absyn_Syntax.lid_equals l1 l2) then begin
(l1, (fun t wp -> wp), (fun t wp -> wp))
end else begin
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _30_181 -> (match (_30_181) with
| (m1, m2, _30_176, _30_178, _30_180) -> begin
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
| Some (_30_184, _30_186, m3, j1, j2) -> begin
(m3, j1, j2)
end)
end)

let monad_leq = (fun env l1 l2 -> if (FStar_Absyn_Syntax.lid_equals l1 l2) then begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end else begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Absyn_Syntax.lid_equals l1 e.msource) && (FStar_Absyn_Syntax.lid_equals l2 e.mtarget)))))
end)

let wp_sig_aux = (fun decls m -> (match ((FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Absyn_Syntax.lid_equals d.FStar_Absyn_Syntax.mname m))))) with
| None -> begin
(let _95_427 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Absyn_Syntax.str)
in (FStar_All.failwith _95_427))
end
| Some (md) -> begin
(match (md.FStar_Absyn_Syntax.signature.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow ((FStar_Util.Inl (a), _30_217)::(FStar_Util.Inl (wp), _30_212)::(FStar_Util.Inl (wlp), _30_207)::[], {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_effect; FStar_Absyn_Syntax.tk = _30_227; FStar_Absyn_Syntax.pos = _30_225; FStar_Absyn_Syntax.fvs = _30_223; FStar_Absyn_Syntax.uvs = _30_221}) -> begin
(a, wp.FStar_Absyn_Syntax.sort)
end
| _30_233 -> begin
(FStar_All.failwith "Impossible")
end)
end))

let wp_signature = (fun env m -> (wp_sig_aux env.effects.decls m))

let default_effect = (fun env l -> (FStar_Util.find_map env.default_effects (fun _30_240 -> (match (_30_240) with
| (l', m) -> begin
if (FStar_Absyn_Syntax.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))

let build_lattice = (fun env se -> (match (se) with
| FStar_Absyn_Syntax.Sig_effect_abbrev (l, _30_245, c, quals, r) -> begin
(match ((FStar_Util.find_map quals (fun _30_2 -> (match (_30_2) with
| FStar_Absyn_Syntax.DefaultEffect (n) -> begin
n
end
| _30_255 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(let _30_259 = env
in {solver = _30_259.solver; range = _30_259.range; curmodule = _30_259.curmodule; gamma = _30_259.gamma; modules = _30_259.modules; expected_typ = _30_259.expected_typ; level = _30_259.level; sigtab = _30_259.sigtab; is_pattern = _30_259.is_pattern; instantiate_targs = _30_259.instantiate_targs; instantiate_vargs = _30_259.instantiate_vargs; effects = _30_259.effects; generalize = _30_259.generalize; letrecs = _30_259.letrecs; top_level = _30_259.top_level; check_uvars = _30_259.check_uvars; use_eq = _30_259.use_eq; is_iface = _30_259.is_iface; admit = _30_259.admit; default_effects = ((e, l))::env.default_effects})
end)
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, _30_263) -> begin
(let effects = (let _30_266 = env.effects
in {decls = (ne)::env.effects.decls; order = _30_266.order; joins = _30_266.joins})
in (let _30_269 = env
in {solver = _30_269.solver; range = _30_269.range; curmodule = _30_269.curmodule; gamma = _30_269.gamma; modules = _30_269.modules; expected_typ = _30_269.expected_typ; level = _30_269.level; sigtab = _30_269.sigtab; is_pattern = _30_269.is_pattern; instantiate_targs = _30_269.instantiate_targs; instantiate_vargs = _30_269.instantiate_vargs; effects = effects; generalize = _30_269.generalize; letrecs = _30_269.letrecs; top_level = _30_269.top_level; check_uvars = _30_269.check_uvars; use_eq = _30_269.use_eq; is_iface = _30_269.is_iface; admit = _30_269.admit; default_effects = _30_269.default_effects}))
end
| FStar_Absyn_Syntax.Sig_sub_effect (sub, _30_273) -> begin
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
in (let find_edge = (fun order _30_301 -> (match (_30_301) with
| (i, j) -> begin
if (FStar_Absyn_Syntax.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _95_484 -> Some (_95_484)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Absyn_Syntax.lid_equals e.msource i) && (FStar_Absyn_Syntax.lid_equals e.mtarget j)))))
end
end))
in (let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _95_492 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Absyn_Syntax.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Absyn_Syntax.lid_equals j k) then begin
[]
end else begin
(match ((let _95_491 = (find_edge order (i, k))
in (let _95_490 = (find_edge order (k, j))
in (_95_491, _95_490)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _30_313 -> begin
[]
end)
end)))
end)))
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
| Some (ub, _30_330, _30_332) -> begin
if ((let _95_501 = (find_edge order (k, ub))
in (FStar_Util.is_some _95_501)) && (not ((let _95_502 = (find_edge order (ub, k))
in (FStar_Util.is_some _95_502))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _30_336 -> begin
bopt
end)) None))
in (match (join_opt) with
| None -> begin
[]
end
| Some (k, e1, e2) -> begin
((i, j, k, e1.mlift, e2.mlift))::[]
end))))))))
in (let effects = (let _30_345 = env.effects
in {decls = _30_345.decls; order = order; joins = joins})
in (let _30_348 = env
in {solver = _30_348.solver; range = _30_348.range; curmodule = _30_348.curmodule; gamma = _30_348.gamma; modules = _30_348.modules; expected_typ = _30_348.expected_typ; level = _30_348.level; sigtab = _30_348.sigtab; is_pattern = _30_348.is_pattern; instantiate_targs = _30_348.instantiate_targs; instantiate_vargs = _30_348.instantiate_vargs; effects = effects; generalize = _30_348.generalize; letrecs = _30_348.letrecs; top_level = _30_348.top_level; check_uvars = _30_348.check_uvars; use_eq = _30_348.use_eq; is_iface = _30_348.is_iface; admit = _30_348.admit; default_effects = _30_348.default_effects})))))))))))))
end
| _30_351 -> begin
env
end))

let rec add_sigelt = (fun env se -> (match (se) with
| FStar_Absyn_Syntax.Sig_bundle (ses, _30_356, _30_358, _30_360) -> begin
(add_sigelts env ses)
end
| _30_364 -> begin
(let lids = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _95_510 = (sigtab env)
in (FStar_Util.smap_add _95_510 l.FStar_Absyn_Syntax.str se))) lids))
end))
and add_sigelts = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))

let empty_lid = (let _95_514 = (let _95_513 = (FStar_Absyn_Syntax.id_of_text "")
in (_95_513)::[])
in (FStar_Absyn_Syntax.lid_of_ids _95_514))

let finish_module = (fun env m -> (let sigs = if (FStar_Absyn_Syntax.lid_equals m.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid) then begin
(FStar_All.pipe_right env.gamma (FStar_List.collect (fun _30_3 -> (match (_30_3) with
| Binding_sig (se) -> begin
(se)::[]
end
| _30_375 -> begin
[]
end))))
end else begin
m.FStar_Absyn_Syntax.exports
end
in (let _30_377 = (add_sigelts env sigs)
in (let _30_379 = env
in {solver = _30_379.solver; range = _30_379.range; curmodule = empty_lid; gamma = []; modules = (m)::env.modules; expected_typ = _30_379.expected_typ; level = _30_379.level; sigtab = _30_379.sigtab; is_pattern = _30_379.is_pattern; instantiate_targs = _30_379.instantiate_targs; instantiate_vargs = _30_379.instantiate_vargs; effects = _30_379.effects; generalize = _30_379.generalize; letrecs = _30_379.letrecs; top_level = _30_379.top_level; check_uvars = _30_379.check_uvars; use_eq = _30_379.use_eq; is_iface = _30_379.is_iface; admit = _30_379.admit; default_effects = _30_379.default_effects}))))

let set_level = (fun env level -> (let _30_383 = env
in {solver = _30_383.solver; range = _30_383.range; curmodule = _30_383.curmodule; gamma = _30_383.gamma; modules = _30_383.modules; expected_typ = _30_383.expected_typ; level = level; sigtab = _30_383.sigtab; is_pattern = _30_383.is_pattern; instantiate_targs = _30_383.instantiate_targs; instantiate_vargs = _30_383.instantiate_vargs; effects = _30_383.effects; generalize = _30_383.generalize; letrecs = _30_383.letrecs; top_level = _30_383.top_level; check_uvars = _30_383.check_uvars; use_eq = _30_383.use_eq; is_iface = _30_383.is_iface; admit = _30_383.admit; default_effects = _30_383.default_effects}))

let is_level = (fun env level -> (env.level = level))

let modules = (fun env -> env.modules)

let current_module = (fun env -> env.curmodule)

let set_current_module = (fun env lid -> (let _30_391 = env
in {solver = _30_391.solver; range = _30_391.range; curmodule = lid; gamma = _30_391.gamma; modules = _30_391.modules; expected_typ = _30_391.expected_typ; level = _30_391.level; sigtab = _30_391.sigtab; is_pattern = _30_391.is_pattern; instantiate_targs = _30_391.instantiate_targs; instantiate_vargs = _30_391.instantiate_vargs; effects = _30_391.effects; generalize = _30_391.generalize; letrecs = _30_391.letrecs; top_level = _30_391.top_level; check_uvars = _30_391.check_uvars; use_eq = _30_391.use_eq; is_iface = _30_391.is_iface; admit = _30_391.admit; default_effects = _30_391.default_effects}))

let set_range = (fun e r -> if (r = FStar_Absyn_Syntax.dummyRange) then begin
e
end else begin
(let _30_395 = e
in {solver = _30_395.solver; range = r; curmodule = _30_395.curmodule; gamma = _30_395.gamma; modules = _30_395.modules; expected_typ = _30_395.expected_typ; level = _30_395.level; sigtab = _30_395.sigtab; is_pattern = _30_395.is_pattern; instantiate_targs = _30_395.instantiate_targs; instantiate_vargs = _30_395.instantiate_vargs; effects = _30_395.effects; generalize = _30_395.generalize; letrecs = _30_395.letrecs; top_level = _30_395.top_level; check_uvars = _30_395.check_uvars; use_eq = _30_395.use_eq; is_iface = _30_395.is_iface; admit = _30_395.admit; default_effects = _30_395.default_effects})
end)

let get_range = (fun e -> e.range)

let find_in_sigtab = (fun env lid -> (let _95_547 = (sigtab env)
in (let _95_546 = (FStar_Absyn_Syntax.text_of_lid lid)
in (FStar_Util.smap_try_find _95_547 _95_546))))

let lookup_bvvdef = (fun env bvvd -> (FStar_Util.find_map env.gamma (fun _30_4 -> (match (_30_4) with
| Binding_var (id, t) when (FStar_Absyn_Util.bvd_eq id bvvd) -> begin
Some (t)
end
| _30_408 -> begin
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

let in_cur_mod = (fun env l -> (let cur = (current_module env)
in if (l.FStar_Absyn_Syntax.nsstr = cur.FStar_Absyn_Syntax.str) then begin
true
end else begin
if (FStar_Util.starts_with l.FStar_Absyn_Syntax.nsstr cur.FStar_Absyn_Syntax.str) then begin
(let lns = (FStar_List.append l.FStar_Absyn_Syntax.ns ((l.FStar_Absyn_Syntax.ident)::[]))
in (let cur = (FStar_List.append cur.FStar_Absyn_Syntax.ns ((cur.FStar_Absyn_Syntax.ident)::[]))
in (let rec aux = (fun c l -> (match ((c, l)) with
| ([], _30_424) -> begin
true
end
| (_30_427, []) -> begin
false
end
| (hd::tl, hd'::tl') when (hd.FStar_Absyn_Syntax.idText = hd'.FStar_Absyn_Syntax.idText) -> begin
(aux tl tl')
end
| _30_438 -> begin
false
end))
in (aux cur lns))))
end else begin
false
end
end))

let lookup_qname = (fun env lid -> (let cur_mod = (in_cur_mod env lid)
in (let found = if cur_mod then begin
(FStar_Util.find_map env.gamma (fun _30_5 -> (match (_30_5) with
| Binding_lid (l, t) -> begin
if (FStar_Absyn_Syntax.lid_equals lid l) then begin
Some (FStar_Util.Inl (t))
end else begin
None
end
end
| Binding_sig (FStar_Absyn_Syntax.Sig_bundle (ses, _30_449, _30_451, _30_453)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _95_574 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _95_574 (FStar_Util.for_some (FStar_Absyn_Syntax.lid_equals lid)))) then begin
Some (FStar_Util.Inr (se))
end else begin
None
end))
end
| Binding_sig (s) -> begin
(let lids = (FStar_Absyn_Util.lids_of_sigelt s)
in if (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Absyn_Syntax.lid_equals lid))) then begin
Some (FStar_Util.Inr (s))
end else begin
None
end)
end
| _30_462 -> begin
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

let lookup_datacon = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_30_470, t, (_30_473, tps, _30_476), _30_479, _30_481, _30_483))) -> begin
(let _95_580 = (FStar_List.map (fun _30_491 -> (match (_30_491) with
| (x, _30_490) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit))
end)) tps)
in (FStar_Absyn_Util.close_typ _95_580 t))
end
| _30_493 -> begin
(let _95_584 = (let _95_583 = (let _95_582 = (name_not_found lid)
in (let _95_581 = (FStar_Absyn_Syntax.range_of_lid lid)
in (_95_582, _95_581)))
in FStar_Absyn_Syntax.Error (_95_583))
in (Prims.raise _95_584))
end))

let lookup_kind_abbrev = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_kind_abbrev (l, binders, k, _30_500))) -> begin
(l, binders, k)
end
| _30_506 -> begin
(let _95_592 = (let _95_591 = (let _95_590 = (name_not_found lid)
in (let _95_589 = (FStar_Absyn_Syntax.range_of_lid lid)
in (_95_590, _95_589)))
in FStar_Absyn_Syntax.Error (_95_591))
in (Prims.raise _95_592))
end))

let lookup_projector = (fun env lid i -> (let fail = (fun _30_511 -> (match (()) with
| () -> begin
(let _95_603 = (let _95_602 = (FStar_Util.string_of_int i)
in (let _95_601 = (FStar_Absyn_Print.sli lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _95_602 _95_601)))
in (FStar_All.failwith _95_603))
end))
in (let t = (lookup_datacon env lid)
in (match ((let _95_604 = (FStar_Absyn_Util.compress_typ t)
in _95_604.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, _30_515) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(let b = (FStar_List.nth binders i)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _95_605 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (FStar_All.pipe_right _95_605 Prims.fst))
end
| FStar_Util.Inr (x) -> begin
(let _95_606 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (FStar_All.pipe_right _95_606 Prims.fst))
end))
end
end
| _30_524 -> begin
(fail ())
end))))

let try_lookup_val_decl = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_30_528, t, q, _30_532))) -> begin
Some ((t, q))
end
| _30_538 -> begin
None
end))

let lookup_val_decl = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_30_542, t, _30_545, _30_547))) -> begin
t
end
| _30_553 -> begin
(let _95_618 = (let _95_617 = (let _95_616 = (name_not_found lid)
in (let _95_615 = (FStar_Absyn_Syntax.range_of_lid lid)
in (_95_616, _95_615)))
in FStar_Absyn_Syntax.Error (_95_617))
in (Prims.raise _95_618))
end))

let lookup_lid = (fun env lid -> (let not_found = (fun _30_557 -> (match (()) with
| () -> begin
(let _95_628 = (let _95_627 = (let _95_626 = (name_not_found lid)
in (let _95_625 = (FStar_Absyn_Syntax.range_of_lid lid)
in (_95_626, _95_625)))
in FStar_Absyn_Syntax.Error (_95_627))
in (Prims.raise _95_628))
end))
in (let mapper = (fun _30_6 -> (match (_30_6) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_30_560, t, (_30_563, tps, _30_566), _30_569, _30_571, _30_573)) -> begin
(let _95_633 = (let _95_632 = (FStar_List.map (fun _30_580 -> (match (_30_580) with
| (x, _30_579) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit))
end)) tps)
in (FStar_Absyn_Util.close_typ _95_632 t))
in Some (_95_633))
end
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (l, t, qs, _30_587)) -> begin
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
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_let ((_30_592, {FStar_Absyn_Syntax.lbname = _30_599; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _30_596; FStar_Absyn_Syntax.lbdef = _30_594}::[]), _30_604, _30_606, _30_608)) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_let ((_30_613, lbs), _30_617, _30_619, _30_621)) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (_30_627) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (lid') -> begin
if (FStar_Absyn_Syntax.lid_equals lid lid') then begin
Some (lb.FStar_Absyn_Syntax.lbtyp)
end else begin
None
end
end)))
end
| t -> begin
None
end))
in (match ((let _95_635 = (lookup_qname env lid)
in (FStar_Util.bind_opt _95_635 mapper))) with
| Some (t) -> begin
(let _30_635 = t
in (let _95_636 = (FStar_Absyn_Syntax.range_of_lid lid)
in {FStar_Absyn_Syntax.n = _30_635.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _30_635.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = _95_636; FStar_Absyn_Syntax.fvs = _30_635.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _30_635.FStar_Absyn_Syntax.uvs}))
end
| None -> begin
(not_found ())
end))))

let is_datacon = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_30_641, _30_643, quals, _30_646))) -> begin
(FStar_All.pipe_right quals (FStar_Util.for_some (fun _30_7 -> (match (_30_7) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _30_654 -> begin
false
end))))
end
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_30_656, t, _30_659, _30_661, _30_663, _30_665))) -> begin
true
end
| _30_671 -> begin
false
end))

let is_record = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_30_675, _30_677, _30_679, _30_681, _30_683, tags, _30_686))) -> begin
(FStar_Util.for_some (fun _30_8 -> (match (_30_8) with
| (FStar_Absyn_Syntax.RecordType (_)) | (FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _30_699 -> begin
false
end)) tags)
end
| _30_701 -> begin
false
end))

let lookup_datacons_of_typ = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_30_705, _30_707, _30_709, _30_711, datas, _30_714, _30_716))) -> begin
(let _95_653 = (FStar_List.map (fun l -> (let _95_652 = (lookup_lid env l)
in (l, _95_652))) datas)
in Some (_95_653))
end
| _30_723 -> begin
None
end))

let lookup_effect_abbrev = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, binders, c, quals, _30_731))) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _30_9 -> (match (_30_9) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _30_739 -> begin
false
end)))) then begin
None
end else begin
Some ((binders, c))
end
end
| _30_741 -> begin
None
end))

let lookup_typ_abbrev = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _30_747, t, quals, _30_751))) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _30_10 -> (match (_30_10) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _30_759 -> begin
false
end)))) then begin
None
end else begin
(let t = (FStar_Absyn_Util.close_with_lam tps t)
in (let _95_664 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named ((t, lid))))
in Some (_95_664)))
end
end
| _30_762 -> begin
None
end))

let lookup_opaque_typ_abbrev = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _30_768, t, quals, _30_772))) -> begin
(let t = (FStar_Absyn_Util.close_with_lam tps t)
in (let _95_669 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named ((t, lid))))
in Some (_95_669)))
end
| _30_779 -> begin
None
end))

let lookup_btvdef = (fun env btvd -> (FStar_Util.find_map env.gamma (fun _30_11 -> (match (_30_11) with
| Binding_typ (id, k) when (FStar_Absyn_Util.bvd_eq id btvd) -> begin
Some (k)
end
| _30_788 -> begin
None
end))))

let lookup_btvar = (fun env btv -> (match ((lookup_btvdef env btv.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _95_681 = (let _95_680 = (let _95_679 = (variable_not_found btv.FStar_Absyn_Syntax.v)
in (_95_679, (FStar_Absyn_Util.range_of_bvd btv.FStar_Absyn_Syntax.v)))
in FStar_Absyn_Syntax.Error (_95_680))
in (Prims.raise _95_681))
end
| Some (k) -> begin
k
end))

let lookup_typ_lid = (fun env ftv -> (match ((lookup_qname env ftv)) with
| (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _, _, _, _)))) | (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, _, _, _)))) -> begin
(FStar_Absyn_Util.close_kind tps k)
end
| _30_822 -> begin
(let _95_689 = (let _95_688 = (let _95_687 = (name_not_found ftv)
in (let _95_686 = (FStar_Absyn_Syntax.range_of_lid ftv)
in (_95_687, _95_686)))
in FStar_Absyn_Syntax.Error (_95_688))
in (Prims.raise _95_689))
end))

let is_projector = (fun env l -> (match ((lookup_qname env l)) with
| (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_, _, _, _, _, quals, _)))) | (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_, _, quals, _)))) -> begin
(FStar_Util.for_some (fun _30_12 -> (match (_30_12) with
| FStar_Absyn_Syntax.Projector (_30_854) -> begin
true
end
| _30_857 -> begin
false
end)) quals)
end
| _30_859 -> begin
false
end))

let try_lookup_effect_lid = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_new_effect (ne, _30_864))) -> begin
(let _95_700 = (FStar_Absyn_Util.close_kind ne.FStar_Absyn_Syntax.binders ne.FStar_Absyn_Syntax.signature)
in (FStar_All.pipe_right _95_700 (fun _95_699 -> Some (_95_699))))
end
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, binders, _30_872, _30_874, _30_876))) -> begin
(let _95_702 = (FStar_Absyn_Util.close_kind binders FStar_Absyn_Syntax.mk_Kind_effect)
in (FStar_All.pipe_right _95_702 (fun _95_701 -> Some (_95_701))))
end
| _30_882 -> begin
None
end))

let lookup_effect_lid = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _95_710 = (let _95_709 = (let _95_708 = (name_not_found ftv)
in (let _95_707 = (FStar_Absyn_Syntax.range_of_lid ftv)
in (_95_708, _95_707)))
in FStar_Absyn_Syntax.Error (_95_709))
in (Prims.raise _95_710))
end
| Some (k) -> begin
k
end))

let lookup_operator = (fun env opname -> (let primName = (FStar_Absyn_Syntax.lid_of_path (("Prims")::((Prims.strcat "_dummy_" opname.FStar_Absyn_Syntax.idText))::[]) FStar_Absyn_Syntax.dummyRange)
in (lookup_lid env primName)))

let push_sigelt = (fun env s -> (build_lattice (let _30_893 = env
in {solver = _30_893.solver; range = _30_893.range; curmodule = _30_893.curmodule; gamma = (Binding_sig (s))::env.gamma; modules = _30_893.modules; expected_typ = _30_893.expected_typ; level = _30_893.level; sigtab = _30_893.sigtab; is_pattern = _30_893.is_pattern; instantiate_targs = _30_893.instantiate_targs; instantiate_vargs = _30_893.instantiate_vargs; effects = _30_893.effects; generalize = _30_893.generalize; letrecs = _30_893.letrecs; top_level = _30_893.top_level; check_uvars = _30_893.check_uvars; use_eq = _30_893.use_eq; is_iface = _30_893.is_iface; admit = _30_893.admit; default_effects = _30_893.default_effects}) s))

let push_local_binding = (fun env b -> (let _30_897 = env
in {solver = _30_897.solver; range = _30_897.range; curmodule = _30_897.curmodule; gamma = (b)::env.gamma; modules = _30_897.modules; expected_typ = _30_897.expected_typ; level = _30_897.level; sigtab = _30_897.sigtab; is_pattern = _30_897.is_pattern; instantiate_targs = _30_897.instantiate_targs; instantiate_vargs = _30_897.instantiate_vargs; effects = _30_897.effects; generalize = _30_897.generalize; letrecs = _30_897.letrecs; top_level = _30_897.top_level; check_uvars = _30_897.check_uvars; use_eq = _30_897.use_eq; is_iface = _30_897.is_iface; admit = _30_897.admit; default_effects = _30_897.default_effects}))

let uvars_in_env = (fun env -> (let no_uvs = (let _95_727 = (FStar_Absyn_Syntax.new_uv_set ())
in (let _95_726 = (FStar_Absyn_Syntax.new_uvt_set ())
in (let _95_725 = (FStar_Absyn_Syntax.new_uvt_set ())
in {FStar_Absyn_Syntax.uvars_k = _95_727; FStar_Absyn_Syntax.uvars_t = _95_726; FStar_Absyn_Syntax.uvars_e = _95_725})))
in (let ext = (fun out uvs -> (let _30_904 = out
in (let _95_734 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_k uvs.FStar_Absyn_Syntax.uvars_k)
in (let _95_733 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_t uvs.FStar_Absyn_Syntax.uvars_t)
in (let _95_732 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_e uvs.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _95_734; FStar_Absyn_Syntax.uvars_t = _95_733; FStar_Absyn_Syntax.uvars_e = _95_732})))))
in (let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_lid (_, t)::tl) | (Binding_var (_, t)::tl) -> begin
(let _95_740 = (let _95_739 = (FStar_Absyn_Util.uvars_in_typ t)
in (ext out _95_739))
in (aux _95_740 tl))
end
| Binding_typ (_30_924, k)::tl -> begin
(let _95_742 = (let _95_741 = (FStar_Absyn_Util.uvars_in_kind k)
in (ext out _95_741))
in (aux _95_742 tl))
end
| Binding_sig (_30_932)::_30_930 -> begin
out
end))
in (aux no_uvs env.gamma)))))

let push_module = (fun env m -> (let _30_937 = (add_sigelts env m.FStar_Absyn_Syntax.exports)
in (let _30_939 = env
in {solver = _30_939.solver; range = _30_939.range; curmodule = _30_939.curmodule; gamma = []; modules = (m)::env.modules; expected_typ = None; level = _30_939.level; sigtab = _30_939.sigtab; is_pattern = _30_939.is_pattern; instantiate_targs = _30_939.instantiate_targs; instantiate_vargs = _30_939.instantiate_vargs; effects = _30_939.effects; generalize = _30_939.generalize; letrecs = _30_939.letrecs; top_level = _30_939.top_level; check_uvars = _30_939.check_uvars; use_eq = _30_939.use_eq; is_iface = _30_939.is_iface; admit = _30_939.admit; default_effects = _30_939.default_effects})))

let set_expected_typ = (fun env t -> (let _30_943 = env
in {solver = _30_943.solver; range = _30_943.range; curmodule = _30_943.curmodule; gamma = _30_943.gamma; modules = _30_943.modules; expected_typ = Some (t); level = _30_943.level; sigtab = _30_943.sigtab; is_pattern = _30_943.is_pattern; instantiate_targs = _30_943.instantiate_targs; instantiate_vargs = _30_943.instantiate_vargs; effects = _30_943.effects; generalize = _30_943.generalize; letrecs = _30_943.letrecs; top_level = _30_943.top_level; check_uvars = _30_943.check_uvars; use_eq = false; is_iface = _30_943.is_iface; admit = _30_943.admit; default_effects = _30_943.default_effects}))

let expected_typ = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

let clear_expected_typ = (fun env -> (let _95_755 = (expected_typ env)
in ((let _30_950 = env
in {solver = _30_950.solver; range = _30_950.range; curmodule = _30_950.curmodule; gamma = _30_950.gamma; modules = _30_950.modules; expected_typ = None; level = _30_950.level; sigtab = _30_950.sigtab; is_pattern = _30_950.is_pattern; instantiate_targs = _30_950.instantiate_targs; instantiate_vargs = _30_950.instantiate_vargs; effects = _30_950.effects; generalize = _30_950.generalize; letrecs = _30_950.letrecs; top_level = _30_950.top_level; check_uvars = _30_950.check_uvars; use_eq = false; is_iface = _30_950.is_iface; admit = _30_950.admit; default_effects = _30_950.default_effects}), _95_755)))

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
(let _95_773 = (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_95_773)::out)
end
| Binding_typ (a, k) -> begin
(let _95_774 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_95_774)::out)
end
| _30_974 -> begin
out
end)) [] env.gamma))

let t_binders = (fun env -> (FStar_List.fold_left (fun out b -> (match (b) with
| Binding_var (_30_979) -> begin
out
end
| Binding_typ (a, k) -> begin
(let _95_779 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_95_779)::out)
end
| _30_986 -> begin
out
end)) [] env.gamma))

let idents = (fun env -> (let _95_783 = (let _95_782 = (binders env)
in (FStar_All.pipe_right _95_782 (FStar_List.map Prims.fst)))
in (FStar_Absyn_Syntax.freevars_of_list _95_783)))

let lidents = (fun env -> (let keys = (FStar_List.fold_left (fun keys _30_13 -> (match (_30_13) with
| Binding_sig (s) -> begin
(let _95_788 = (FStar_Absyn_Util.lids_of_sigelt s)
in (FStar_List.append _95_788 keys))
end
| _30_994 -> begin
keys
end)) [] env.gamma)
in (let _95_793 = (sigtab env)
in (FStar_Util.smap_fold _95_793 (fun _30_996 v keys -> (let _95_792 = (FStar_Absyn_Util.lids_of_sigelt v)
in (FStar_List.append _95_792 keys))) keys))))




